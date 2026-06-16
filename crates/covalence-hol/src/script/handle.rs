//! [`LazyEnv`] — an **in-progress** environment whose theorem bindings may
//! still be computing. Each binding is a [`ThmHandle`]: a ready `Thm`, or a
//! future (e.g. a `#compute` running on a blocking thread). The Ready/Pending
//! representation is **encapsulated** — callers only ever use the async
//! getters, so an entry that is still running is awaited transparently.
//!
//! This is the seed of the async-prover env: when a theorem *yields* (a
//! long-running `#compute`/observer), its handle goes here and the next
//! statement proceeds; a later reference simply awaits it.

use covalence_core::Thm;
use futures::FutureExt;
use futures::future::{BoxFuture, Shared};

use super::ScriptError;

/// A handle to a theorem: already proved, or still being computed (a shared
/// future, so several consumers can await the same computation).
#[derive(Clone)]
enum ThmHandle {
    Ready(Thm),
    Pending(Shared<BoxFuture<'static, Result<Thm, ScriptError>>>),
}

/// An in-progress environment of theorem handles. Cloning is cheap (an `imbl`
/// persistent map of clonable handles); the Ready/Pending split is private.
#[derive(Clone, Default)]
pub struct LazyEnv {
    lemmas: imbl::HashMap<String, ThmHandle>,
}

impl LazyEnv {
    /// An empty handle environment.
    pub fn new() -> Self {
        Self::default()
    }

    /// Whether this environment binds nothing.
    pub fn is_empty(&self) -> bool {
        self.lemmas.is_empty()
    }

    /// Bind `name` to an already-proved theorem.
    pub fn insert_ready(&mut self, name: impl Into<String>, thm: Thm) {
        self.lemmas.insert(name.into(), ThmHandle::Ready(thm));
    }

    /// Bind `name` to a computation running on a blocking thread (a `#compute`
    /// / `spawn_blocking` task). The binding is *pending* until the task
    /// finishes; [`LazyEnv::get`] awaits it.
    pub fn insert_compute(
        &mut self,
        name: impl Into<String>,
        task: tokio::task::JoinHandle<Result<Thm, ScriptError>>,
    ) {
        let fut = async move {
            task.await
                .map_err(|e| ScriptError::Syntax(format!("#compute task failed: {e}")))?
        }
        .boxed()
        .shared();
        self.lemmas.insert(name.into(), ThmHandle::Pending(fut));
    }

    /// Whether `name` is bound (ready or pending).
    pub fn contains(&self, name: &str) -> bool {
        self.lemmas.contains_key(name)
    }

    /// The bound names, in arbitrary order.
    pub fn names(&self) -> impl Iterator<Item = &String> {
        self.lemmas.keys()
    }

    /// **Async getter:** the theorem bound to `name`, awaiting its computation
    /// if still pending. `None` if `name` is unbound.
    pub async fn get(&self, name: &str) -> Option<Result<Thm, ScriptError>> {
        match self.lemmas.get(name)? {
            ThmHandle::Ready(t) => Some(Ok(t.clone())),
            ThmHandle::Pending(f) => Some(f.clone().await),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_core::{Term, Thm};

    fn rt() -> tokio::runtime::Runtime {
        tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap()
    }

    /// A trivial theorem `⊢ 0 = 0`.
    fn refl0() -> Thm {
        Thm::refl(Term::nat_lit(0u64)).unwrap()
    }

    #[test]
    fn ready_binding_is_returned_directly() {
        rt().block_on(async {
            let mut e = LazyEnv::new();
            assert!(e.is_empty());
            e.insert_ready("x", refl0());
            assert!(e.contains("x"));
            let thm = e.get("x").await.unwrap().unwrap();
            assert_eq!(thm.concl(), refl0().concl());
            assert!(e.get("missing").await.is_none());
        });
    }

    #[test]
    fn pending_compute_is_awaited_transparently() {
        rt().block_on(async {
            let mut e = LazyEnv::new();
            // A computation on a blocking thread — the getter awaits it.
            let task = tokio::task::spawn_blocking(|| Ok(refl0()));
            e.insert_compute("y", task);
            assert!(e.contains("y"));
            let thm = e.get("y").await.unwrap().unwrap();
            assert_eq!(thm.concl(), refl0().concl());
            // The shared future is multi-await: a second get still resolves.
            let again = e.get("y").await.unwrap().unwrap();
            assert_eq!(again.concl(), refl0().concl());
        });
    }

    #[test]
    fn compute_error_propagates_through_the_getter() {
        rt().block_on(async {
            let mut e = LazyEnv::new();
            let task = tokio::task::spawn_blocking(|| Err(ScriptError::Syntax("boom".into())));
            e.insert_compute("bad", task);
            let err = e.get("bad").await.unwrap().unwrap_err();
            assert!(matches!(err, ScriptError::Syntax(ref m) if m == "boom"));
        });
    }
}
