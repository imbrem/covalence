//! Host-side implementation of the `cov:pure@0.1.0` WIT package.
//!
//! See `wit/pure.wit` for the interface. This module:
//!
//! - Generates the wasmtime bindings via `bindgen!`.
//! - Implements the resource `Host*` traits on [`PureHost`], wiring
//!   the WIT surface to the kernel's `Type` / `Term` / `Thm` /
//!   `Ctx` directly — no host-side newtype wrappers.
//!
//! Resources are stored in a `ResourceTable`, so identity is by table
//! key, not by Rust pointer. The kernel's α-equivalence rules treat
//! distinct `term` handles for α-equivalent contents as equal — that
//! semantics is preserved end-to-end.

use wasmtime::component::{Resource, ResourceTable};

// Re-exported `pub use` because the `bindgen!` macro below generates
// internal `pub use Type as __with_nameN;` re-exports for every entry
// in its `with:` mapping; a plain `use` would leave those re-exports
// pointing at a private import.
pub use covalence_core::{Term, Ctx, Thm, Type};
use covalence_core::Error;

// Resource keys in `with:` use dot (not slash) between interface and
// resource. `imports: { default: trappable }` makes WIT methods that
// return `result<T, string>` map to `wasmtime::Result<Result<T, String>>`.
wasmtime::component::bindgen!({
    path: "wit/pure.wit",
    world: "pure-guest",
    with: {
        "cov:pure/api.pure-type": Type,
        "cov:pure/api.term": Term,
        "cov:pure/api.ctx": Ctx,
        "cov:pure/api.thm": Thm,
    },
    imports: { default: trappable },
});

/// State the host carries while serving `cov:pure` calls. Per-host
/// `ResourceTable` so theorems built across many calls share identity.
pub struct PureHost {
    table: ResourceTable,
}

impl PureHost {
    pub fn new() -> Self {
        Self {
            table: ResourceTable::new(),
        }
    }

    pub fn table(&self) -> &ResourceTable {
        &self.table
    }

    pub fn table_mut(&mut self) -> &mut ResourceTable {
        &mut self.table
    }

    fn push_type(&mut self, t: Type) -> wasmtime::Result<Resource<Type>> {
        self.table.push(t).map_err(wasmtime::Error::from)
    }

    fn push_term(&mut self, t: Term) -> wasmtime::Result<Resource<Term>> {
        self.table.push(t).map_err(wasmtime::Error::from)
    }

    fn push_thm(&mut self, t: Thm) -> wasmtime::Result<Resource<Thm>> {
        self.table.push(t).map_err(wasmtime::Error::from)
    }

    fn push_term_set(&mut self, t: Ctx) -> wasmtime::Result<Resource<Ctx>> {
        self.table.push(t).map_err(wasmtime::Error::from)
    }
}

impl Default for PureHost {
    fn default() -> Self {
        Self::new()
    }
}

// bindgen wraps each trappable-import body in `wasmtime::Result<...>`.
// Outer = trap signal, inner = WIT-level `result<T, string>`.
type Trappable<T> = wasmtime::Result<Result<T, String>>;

fn err_str(e: Error) -> String {
    format!("{}", e)
}

// ============================================================================
// Interface trait — the `api` interface has no top-level functions.
// ============================================================================

impl cov::pure::api::Host for PureHost {}

// ============================================================================
// pure-type
// ============================================================================

impl cov::pure::api::HostPureType for PureHost {
    fn tfree(&mut self, name: String) -> wasmtime::Result<Resource<Type>> {
        self.push_type(Type::tfree(&name))
    }

    fn prop(&mut self) -> wasmtime::Result<Resource<Type>> {
        self.push_type(Type::prop())
    }

    fn bytes(&mut self) -> wasmtime::Result<Resource<Type>> {
        self.push_type(Type::bytes())
    }

    fn fun(
        &mut self,
        dom: Resource<Type>,
        cod: Resource<Type>,
    ) -> wasmtime::Result<Resource<Type>> {
        let d = self.table.get(&dom)?.clone();
        let c = self.table.get(&cod)?.clone();
        self.push_type(Type::fun(d, c))
    }

    fn tycon(
        &mut self,
        name: String,
        args: Vec<Resource<Type>>,
    ) -> wasmtime::Result<Resource<Type>> {
        let mut v = Vec::with_capacity(args.len());
        for r in &args {
            v.push(self.table.get(r)?.clone());
        }
        self.push_type(Type::tycon(&name, v))
    }

    fn equals(
        &mut self,
        this: Resource<Type>,
        other: Resource<Type>,
    ) -> wasmtime::Result<bool> {
        let a = self.table.get(&this)?;
        let b = self.table.get(&other)?;
        Ok(a == b)
    }

    fn is_prop(&mut self, this: Resource<Type>) -> wasmtime::Result<bool> {
        Ok(self.table.get(&this)?.is_prop())
    }

    fn render(&mut self, this: Resource<Type>) -> wasmtime::Result<String> {
        Ok(format!("{}", self.table.get(&this)?))
    }

    fn drop(&mut self, rep: Resource<Type>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}

// ============================================================================
// term
// ============================================================================

impl cov::pure::api::HostTerm for PureHost {
    fn bound(&mut self, idx: u32) -> wasmtime::Result<Resource<Term>> {
        self.push_term(Term::bound(idx))
    }

    fn free(
        &mut self,
        name: String,
        ty: Resource<Type>,
    ) -> wasmtime::Result<Resource<Term>> {
        let ty = self.table.get(&ty)?.clone();
        self.push_term(Term::free(&name, ty))
    }

    fn mk_const(
        &mut self,
        name: String,
        ty: Resource<Type>,
    ) -> wasmtime::Result<Resource<Term>> {
        let ty = self.table.get(&ty)?.clone();
        self.push_term(Term::const_(&name, ty))
    }

    fn app(
        &mut self,
        fun: Resource<Term>,
        arg: Resource<Term>,
    ) -> wasmtime::Result<Resource<Term>> {
        let f = self.table.get(&fun)?.clone();
        let a = self.table.get(&arg)?.clone();
        self.push_term(Term::app(f, a))
    }

    fn abs(
        &mut self,
        hint: String,
        ty: Resource<Type>,
        body: Resource<Term>,
    ) -> wasmtime::Result<Resource<Term>> {
        let ty = self.table.get(&ty)?.clone();
        let body = self.table.get(&body)?.clone();
        self.push_term(Term::abs(ty, body))
    }

    fn imp(
        &mut self,
        lhs: Resource<Term>,
        rhs: Resource<Term>,
    ) -> wasmtime::Result<Resource<Term>> {
        let l = self.table.get(&lhs)?.clone();
        let r = self.table.get(&rhs)?.clone();
        self.push_term(Term::imp(l, r))
    }

    fn all(
        &mut self,
        hint: String,
        ty: Resource<Type>,
        body: Resource<Term>,
    ) -> wasmtime::Result<Resource<Term>> {
        let ty = self.table.get(&ty)?.clone();
        let body = self.table.get(&body)?.clone();
        self.push_term(Term::all(&hint, ty, body))
    }

    fn mk_eq(
        &mut self,
        lhs: Resource<Term>,
        rhs: Resource<Term>,
    ) -> wasmtime::Result<Resource<Term>> {
        let l = self.table.get(&lhs)?.clone();
        let r = self.table.get(&rhs)?.clone();
        self.push_term(Term::eq(l, r))
    }

    fn blob(&mut self, bytes: Vec<u8>) -> wasmtime::Result<Resource<Term>> {
        // `Vec<u8>` -> `bytes::Bytes` is the zero-copy `From` impl in `bytes`.
        self.push_term(Term::blob(bytes))
    }

    fn type_of(&mut self, this: Resource<Term>) -> Trappable<Resource<Type>> {
        let t = self.table.get(&this)?.clone();
        match t.type_of() {
            Ok(ty) => Ok(Ok(self.push_type(ty)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn equals(
        &mut self,
        this: Resource<Term>,
        other: Resource<Term>,
    ) -> wasmtime::Result<bool> {
        let a = self.table.get(&this)?;
        let b = self.table.get(&other)?;
        Ok(a == b)
    }

    fn has_no_obs(&mut self, this: Resource<Term>) -> wasmtime::Result<bool> {
        Ok(self.table.get(&this)?.has_no_obs())
    }

    fn render(&mut self, this: Resource<Term>) -> wasmtime::Result<String> {
        Ok(format!("{}", self.table.get(&this)?))
    }

    fn drop(&mut self, rep: Resource<Term>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}

// ============================================================================
// ctx
// ============================================================================

impl cov::pure::api::HostCtx for PureHost {
    fn len(&mut self, this: Resource<Ctx>) -> wasmtime::Result<u32> {
        Ok(self.table.get(&this)?.len() as u32)
    }

    fn is_empty(&mut self, this: Resource<Ctx>) -> wasmtime::Result<bool> {
        Ok(self.table.get(&this)?.is_empty())
    }

    fn contains(
        &mut self,
        this: Resource<Ctx>,
        t: Resource<Term>,
    ) -> wasmtime::Result<bool> {
        let needle = self.table.get(&t)?.clone();
        Ok(self.table.get(&this)?.contains(&needle))
    }

    fn at(
        &mut self,
        this: Resource<Ctx>,
        idx: u32,
    ) -> wasmtime::Result<Option<Resource<Term>>> {
        let got = self.table.get(&this)?.at(idx as usize).cloned();
        match got {
            Some(t) => Ok(Some(self.push_term(t)?)),
            None => Ok(None),
        }
    }

    fn drop(&mut self, rep: Resource<Ctx>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}

// ============================================================================
// thm
// ============================================================================

impl cov::pure::api::HostThm for PureHost {
    // ---- LF rules ----

    fn assume(&mut self, phi: Resource<Term>) -> Trappable<Resource<Thm>> {
        let phi = self.table.get(&phi)?.clone();
        match Thm::assume(phi) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn imp_intro(
        &mut self,
        this: Resource<Thm>,
        phi: Resource<Term>,
    ) -> Trappable<Resource<Thm>> {
        let thm = self.table.get(&this)?.clone();
        let phi = self.table.get(&phi)?.clone();
        match thm.imp_intro(&phi) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn imp_elim(
        &mut self,
        this: Resource<Thm>,
        hyp: Resource<Thm>,
    ) -> Trappable<Resource<Thm>> {
        let thm = self.table.get(&this)?.clone();
        let hyp = self.table.get(&hyp)?.clone();
        match thm.imp_elim(hyp) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn all_intro(
        &mut self,
        this: Resource<Thm>,
        name: String,
        ty: Resource<Type>,
    ) -> Trappable<Resource<Thm>> {
        let thm = self.table.get(&this)?.clone();
        let ty = self.table.get(&ty)?.clone();
        match thm.all_intro(&name, ty) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn all_elim(
        &mut self,
        this: Resource<Thm>,
        witness: Resource<Term>,
    ) -> Trappable<Resource<Thm>> {
        let thm = self.table.get(&this)?.clone();
        let witness = self.table.get(&witness)?.clone();
        match thm.all_elim(witness) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    // ---- Equality rules ----

    fn refl(&mut self, t: Resource<Term>) -> Trappable<Resource<Thm>> {
        let t = self.table.get(&t)?.clone();
        match Thm::refl(t) {
            Ok(th) => Ok(Ok(self.push_thm(th)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn trans(
        &mut self,
        this: Resource<Thm>,
        other: Resource<Thm>,
    ) -> Trappable<Resource<Thm>> {
        let a = self.table.get(&this)?.clone();
        let b = self.table.get(&other)?.clone();
        match a.trans(b) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn sym(&mut self, this: Resource<Thm>) -> Trappable<Resource<Thm>> {
        let a = self.table.get(&this)?.clone();
        match a.sym() {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn cong_app(
        &mut self,
        this: Resource<Thm>,
        arg: Resource<Thm>,
    ) -> Trappable<Resource<Thm>> {
        let a = self.table.get(&this)?.clone();
        let b = self.table.get(&arg)?.clone();
        match a.cong_app(b) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn cong_abs(
        &mut self,
        this: Resource<Thm>,
        name: String,
        ty: Resource<Type>,
    ) -> Trappable<Resource<Thm>> {
        let a = self.table.get(&this)?.clone();
        let ty = self.table.get(&ty)?.clone();
        match a.cong_abs(&name, ty) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn beta_conv(&mut self, app: Resource<Term>) -> Trappable<Resource<Thm>> {
        let a = self.table.get(&app)?.clone();
        match Thm::beta_conv(a) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn eta_conv(&mut self, abs: Resource<Term>) -> Trappable<Resource<Thm>> {
        let a = self.table.get(&abs)?.clone();
        match Thm::eta_conv(a) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn inst_tfree(
        &mut self,
        this: Resource<Thm>,
        name: String,
        replacement: Resource<Type>,
    ) -> Trappable<Resource<Thm>> {
        let a = self.table.get(&this)?.clone();
        let r = self.table.get(&replacement)?.clone();
        match a.inst_tfree(&name, r) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    // ---- Accessors ----

    fn hyps(&mut self, this: Resource<Thm>) -> wasmtime::Result<Resource<Ctx>> {
        let hyps = self.table.get(&this)?.hyps().clone();
        self.push_term_set(hyps)
    }

    fn concl(&mut self, this: Resource<Thm>) -> wasmtime::Result<Resource<Term>> {
        let c = self.table.get(&this)?.concl().clone();
        self.push_term(c)
    }

    fn has_no_obs(&mut self, this: Resource<Thm>) -> wasmtime::Result<bool> {
        Ok(self.table.get(&this)?.has_no_obs())
    }

    fn render(&mut self, this: Resource<Thm>) -> wasmtime::Result<String> {
        Ok(format!("{}", self.table.get(&this)?))
    }

    fn drop(&mut self, rep: Resource<Thm>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}
