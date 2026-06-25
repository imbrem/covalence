//! Lazy environment values — a value is either **ready**, or still being
//! **computed** (a shared future). [`Lazy<T>`] is the value; [`LazyMap<T>`] is
//! a name→`Lazy<T>` store with **async** getters (the Ready/Pending split is
//! encapsulated — a caller just `get(name).await`s and a still-running entry is
//! awaited transparently).
//!
//! This is the future-holding backing of an [`super::Env`]: its **single**
//! namespace map holds every definition kind (consts, lemmas, tactics, rules)
//! as a `LazyMap`, so any binding can still be **computing** — today only
//! `#spawn`-ing lemmas, but the same machinery covers "one async task per
//! definition" (e.g. a `bytes` const loaded from the network) with no new code.

use covalence_core::Thm;
use futures::FutureExt;
use futures::future::{BoxFuture, Shared};

use super::ScriptError;

/// A lazily-computed value: **ready** (an `Ok` value — or a held `Err`, so a
/// failed definition can be reported *later*, grouped with others, à la
/// Python's `ExceptionGroup`), or still being **computed** (a `Shared` future,
/// so several consumers await the same computation).
#[derive(Clone)]
pub(super) enum Lazy<T: Clone> {
    Ready(Result<T, ScriptError>),
    Pending(Shared<BoxFuture<'static, Result<T, ScriptError>>>),
}

/// A lazily-computed theorem (a `#spawn`-ing or proved lemma).
#[allow(dead_code)]
pub(super) type LazyThm = Lazy<Thm>;

/// A name→[`Lazy<T>`] map with async getters. Cloning is cheap (an `imbl`
/// persistent map of clonable handles). The bound `T: Clone + Send + Sync +
/// 'static` is what `Shared` needs.
#[derive(Clone)]
pub(super) struct LazyMap<T: Clone> {
    entries: imbl::HashMap<String, Lazy<T>>,
}

impl<T: Clone> Default for LazyMap<T> {
    fn default() -> Self {
        LazyMap {
            entries: imbl::HashMap::new(),
        }
    }
}

impl<T: Clone + Send + Sync + 'static> LazyMap<T> {
    /// An empty map.
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self::default()
    }

    /// Whether this map binds nothing.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Bind `name` to an already-available value.
    pub fn insert_ready(&mut self, name: impl Into<String>, value: T) {
        self.entries.insert(name.into(), Lazy::Ready(Ok(value)));
    }

    /// Bind `name` to an already-known **failure**, held for deferred /
    /// grouped reporting (the error surfaces when the binding is looked up).
    #[allow(dead_code)]
    pub fn insert_failed(&mut self, name: impl Into<String>, err: ScriptError) {
        self.entries.insert(name.into(), Lazy::Ready(Err(err)));
    }

    /// Bind `name` to a value still being **computed** (a future). The binding
    /// is *pending* until the future resolves; [`LazyMap::get`] awaits it (the
    /// future is `Shared`, so several consumers await the same computation).
    pub fn insert_pending(
        &mut self,
        name: impl Into<String>,
        fut: BoxFuture<'static, Result<T, ScriptError>>,
    ) {
        self.entries
            .insert(name.into(), Lazy::Pending(fut.shared()));
    }

    /// Whether `name` is bound (ready or pending).
    pub fn contains(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// The bound names, in arbitrary order.
    #[allow(dead_code)]
    pub fn names(&self) -> impl Iterator<Item = &String> {
        self.entries.keys()
    }

    /// **Async getter:** the value bound to `name`, awaiting its computation if
    /// still pending. `None` if `name` is unbound.
    pub async fn get(&self, name: &str) -> Option<Result<T, ScriptError>> {
        match self.entries.get(name)? {
            Lazy::Ready(r) => Some(r.clone()),
            Lazy::Pending(f) => Some(f.clone().await),
        }
    }

    /// Synchronous peek: the value bound to `name` **only if already ready and
    /// successful** (not still computing, not a held error).
    pub fn get_ready(&self, name: &str) -> Option<T> {
        match self.entries.get(name)? {
            Lazy::Ready(Ok(t)) => Some(t.clone()),
            _ => None,
        }
    }

    /// Merge another map's bindings in (cheap — handles are clonable; shadows
    /// existing entries of the same name).
    pub fn merge(&mut self, other: &LazyMap<T>) {
        self.entries
            .extend(other.entries.iter().map(|(k, v)| (k.clone(), v.clone())));
    }

    /// Merge another's bindings in, each name qualified by `prefix`
    /// (`prefix.name`), or unchanged if `prefix` is empty.
    pub fn merge_prefixed(&mut self, other: &LazyMap<T>, prefix: &str) {
        for (k, v) in &other.entries {
            let key = if prefix.is_empty() {
                k.clone()
            } else {
                format!("{prefix}.{k}")
            };
            self.entries.insert(key, v.clone());
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
            let mut e: LazyMap<Thm> = LazyMap::new();
            assert!(e.is_empty());
            e.insert_ready("x", refl0());
            assert!(e.contains("x"));
            assert_eq!(e.get_ready("x").unwrap().concl(), refl0().concl());
            let thm = e.get("x").await.unwrap().unwrap();
            assert_eq!(thm.concl(), refl0().concl());
            assert!(e.get("missing").await.is_none());
        });
    }

    #[test]
    fn pending_compute_is_awaited_transparently() {
        rt().block_on(async {
            let mut e: LazyMap<Thm> = LazyMap::new();
            // A still-computing binding — the getter awaits it.
            e.insert_pending("y", async { Ok(refl0()) }.boxed());
            assert!(e.contains("y"));
            assert!(e.get_ready("y").is_none(), "pending until awaited");
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
            let mut e: LazyMap<Thm> = LazyMap::new();
            e.insert_pending(
                "bad",
                async { Err(ScriptError::Syntax("boom".into())) }.boxed(),
            );
            let err = e.get("bad").await.unwrap().unwrap_err();
            assert!(matches!(err, ScriptError::Syntax(ref m) if m == "boom"));
        });
    }
}
