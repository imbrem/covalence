//! End-to-end smoke test: build a tree, mount it, ls/read through the kernel.
//!
//! Requires `fusermount3` on PATH and a working `/dev/fuse`. If the mount
//! returns an error that smells like "no FUSE available," the test prints
//! a skip notice and passes — this keeps the suite green on bare CI envs
//! without losing local-dev coverage.

#![cfg(target_os = "linux")]

use std::os::unix::fs::MetadataExt;
use std::time::Duration;

use covalence_fuse::{TreeFsConfig, mount_tree};
use covalence_hash::O256;
use covalence_object::{Dir, DirMode, DirRow, TableBuilder};
use covalence_store::{BlobStore, ContentStore, SharedMemoryStore};

/// Build a small tree in a shared in-memory store and return (root_hash, store).
///
/// Layout:
/// ```text
/// /
///   hello.txt           "hello, covalence!\n"
///   src/                (subdir)
///     main.rs           "fn main() { println!(\"hi\"); }\n"
/// ```
fn build_fixture() -> (O256, BlobStore<O256>) {
    let store = SharedMemoryStore::new();

    let hello_bytes = b"hello, covalence!\n";
    let hello_hash = store.insert(hello_bytes).expect("insert hello");

    let main_bytes = b"fn main() { println!(\"hi\"); }\n";
    let main_hash = store.insert(main_bytes).expect("insert main");

    // Subdir: src/
    let mut src_builder = TableBuilder::new(Dir);
    src_builder.push_row(DirRow {
        name: b"main.rs".to_vec(),
        mode: DirMode::REGULAR,
        child: main_hash,
    });
    let src_table = src_builder.build();
    let src_bytes = src_table.as_bytes().to_vec();
    let src_hash = store.insert(&src_bytes).expect("insert src");

    // Root tree.
    let mut root_builder = TableBuilder::new(Dir);
    root_builder.push_row(DirRow {
        name: b"hello.txt".to_vec(),
        mode: DirMode::REGULAR,
        child: hello_hash,
    });
    root_builder.push_row(DirRow {
        name: b"src".to_vec(),
        mode: DirMode::DIR,
        child: src_hash,
    });
    let root_table = root_builder.build();
    let root_bytes = root_table.as_bytes().to_vec();
    let root_hash = store.insert(&root_bytes).expect("insert root");

    (root_hash, BlobStore::new(store))
}

/// Decide whether a `mount_tree` error means "FUSE isn't available here" so
/// the test can skip rather than fail. The signatures we care about:
/// - `fusermount3` not on PATH
/// - `/dev/fuse` not present / permission denied
fn is_fuse_unavailable(err: &std::io::Error) -> bool {
    let msg = err.to_string().to_lowercase();
    msg.contains("fusermount")
        || msg.contains("/dev/fuse")
        || msg.contains("no such device")
        || matches!(
            err.kind(),
            std::io::ErrorKind::NotFound | std::io::ErrorKind::PermissionDenied
        )
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn mount_tree_and_read() {
    let _ = tracing_subscriber::fmt::try_init();
    let (root, store) = build_fixture();
    let mountpoint = tempfile::tempdir().expect("tempdir");
    let mountpoint_path = mountpoint.path().to_path_buf();

    let cfg = TreeFsConfig::default();

    // Spawn the mount on a background task; it blocks until the session ends.
    let mount_path_for_task = mountpoint_path.clone();
    let mount_task =
        tokio::spawn(async move { mount_tree(store, root, &mount_path_for_task, cfg).await });

    // Wait for the mount to become live. fuse3's `mount_with_unprivileged`
    // returns as soon as the fusermount3 child reports success, but the
    // kernel still has a small window before the mount is visible to other
    // syscalls on this process. Poll by stat-ing the mountpoint and checking
    // whether the *device id* changed — that flips the moment the kernel
    // splices the mount in.
    let outer_dev = std::fs::metadata(&mountpoint_path)
        .expect("stat outer")
        .dev();
    let mut ready = false;
    for _ in 0..100 {
        tokio::time::sleep(Duration::from_millis(50)).await;
        if mount_task.is_finished() {
            let res = mount_task.await.expect("join");
            match res {
                Ok(()) => panic!("mount returned Ok before we read anything"),
                Err(e) if is_fuse_unavailable(&e) => {
                    eprintln!("skipping: FUSE unavailable in this environment: {e}");
                    return;
                }
                Err(e) => panic!("mount failed: {e}"),
            }
        }
        if let Ok(md) = std::fs::metadata(&mountpoint_path) {
            if md.dev() != outer_dev {
                ready = true;
                break;
            }
        }
    }
    assert!(ready, "mount never became live within 5s");

    // Use spawn_blocking for std::fs calls so we don't block the runtime.
    let mp = mountpoint_path.clone();
    let result = tokio::task::spawn_blocking(move || -> std::io::Result<()> {
        // Diagnostic: dump /proc/self/mounts for the mountpoint
        if let Ok(mounts) = std::fs::read_to_string("/proc/self/mounts") {
            let mp_str = mp.to_string_lossy();
            for line in mounts.lines() {
                if line.contains(&*mp_str) {
                    eprintln!("MOUNTS: {line}");
                }
            }
        }
        let md = std::fs::metadata(&mp)?;
        eprintln!(
            "mp metadata: dev={} ino={} mode={:o}",
            md.dev(),
            md.ino(),
            md.mode()
        );

        // readdir at root
        let mut entries: Vec<String> = std::fs::read_dir(&mp)?
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .collect();
        eprintln!("read_dir entries: {entries:?}");
        entries.sort();
        assert_eq!(entries, vec!["hello.txt".to_string(), "src".to_string()]);

        // read hello.txt
        let hello = std::fs::read(mp.join("hello.txt"))?;
        assert_eq!(hello, b"hello, covalence!\n");

        // recurse into src/
        let mut src_entries: Vec<String> = std::fs::read_dir(mp.join("src"))?
            .filter_map(|e| e.ok())
            .map(|e| e.file_name().to_string_lossy().into_owned())
            .collect();
        src_entries.sort();
        assert_eq!(src_entries, vec!["main.rs".to_string()]);

        // read src/main.rs
        let main = std::fs::read(mp.join("src/main.rs"))?;
        assert_eq!(main, b"fn main() { println!(\"hi\"); }\n");

        // Ranged pread via seek+read_exact. `std::fs::read` issues
        // `read(off=0, size=4096)` for our tiny fixture files so it
        // never exercises offset > 0; seek + read_exact does.
        use std::io::{Read, Seek, SeekFrom};
        let mut f = std::fs::File::open(mp.join("hello.txt"))?;
        f.seek(SeekFrom::Start(7))?;
        let mut buf = [0u8; 11];
        f.read_exact(&mut buf)?;
        assert_eq!(&buf, b"covalence!\n");

        // lookup a name that does not exist
        let missing = std::fs::metadata(mp.join("does-not-exist"));
        assert!(missing.is_err(), "missing name should error");
        assert_eq!(
            missing.unwrap_err().kind(),
            std::io::ErrorKind::NotFound,
            "missing name should map to ENOENT, not EIO"
        );

        Ok(())
    })
    .await
    .expect("join blocking");

    // Drop the mount before asserting so we always clean up.
    mount_task.abort();
    let _ = tokio::time::timeout(Duration::from_secs(2), mount_task).await;
    // Best-effort fusermount3 -u in case Drop didn't finish before tempdir cleanup.
    let _ = std::process::Command::new("fusermount3")
        .args(["-u", &mountpoint_path.to_string_lossy()])
        .status();

    result.expect("filesystem operations failed");
}
