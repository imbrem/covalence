(component
    (import "attest" (func $attest))
    (import "cov:blob/api" (instance $blob-api
        (export "blob" (type (sub resource)))
        (export "[method]blob.read" (func (param "self" (borrow 0)) (result (list u8))))
        (export "[method]blob.eq" (func (param "self" (borrow 0)) (param "other" (borrow 0)) (result bool)))
    ))
    (alias export $blob-api "blob" (type $blob))
    (alias export $blob-api "[method]blob.read" (func $blob-read))
    (import "blob-{hash_hex}" (func $get-blob (result (own $blob))))

    ;; Allocator module provides memory and realloc for list lowering
    (core module $alloc_mod
        (memory 1)
        (export "memory" (memory 0))
        (func $realloc (param i32 i32 i32 i32) (result i32)
            (i32.const 0x1000)
        )
        (export "cabi_realloc" (func $realloc))
    )
    (core instance $alloc (instantiate $alloc_mod))
    (alias core export $alloc "memory" (core memory $mem))
    (alias core export $alloc "cabi_realloc" (core func $realloc_fn))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $get_blob_lowered (canon lower (func $get-blob)))
    (core func $blob_read_lowered (canon lower (func $blob-read) (memory $mem) (realloc $realloc_fn)))
    (core func $blob_drop_lowered (canon resource.drop $blob))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "get-blob" (func $get_blob (result i32)))
        ;; canon lower with retptr ABI: (borrow_handle, retptr) -> ()
        (import "env" "blob-read" (func $blob_read (param i32 i32)))
        (import "env" "blob-drop" (func $blob_drop (param i32)))
        (func $start
            (local $handle i32)
            ;; Get a blob handle
            (local.set $handle (call $get_blob))
            ;; Call read — writes (ptr, len) at retptr offset 0
            (call $blob_read (local.get $handle) (i32.const 0))
            ;; Drop the blob handle
            (call $blob_drop (local.get $handle))
            ;; If we got here without trapping, the read succeeded — attest
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "get-blob" (func $get_blob_lowered))
            (export "blob-read" (func $blob_read_lowered))
            (export "blob-drop" (func $blob_drop_lowered))
        ))
    ))
)
