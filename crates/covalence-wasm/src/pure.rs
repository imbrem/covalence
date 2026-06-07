//! Host-side implementation of the `cov:pure@0.1.0` WIT package.
//!
//! See `wit/pure.wit` for the interface. This module:
//!
//! - Generates the wasmtime bindings via `bindgen!`.
//! - Implements the resource `Host*` traits on [`PureHost`], wiring
//!   the WIT surface to `covalence_pure`'s `Type`/`Term`/`Thm`.
//! - Backs hypothesis sets with `Arc<BTreeSet<Term>>` (opaque to the
//!   guest — see [`HostTermSet`]).
//!
//! Resources are stored in a `ResourceTable`, so identity is by table
//! key, not by Rust pointer. The kernel's α-equivalence rules treat
//! distinct `term` handles for α-equivalent contents as equal — that
//! semantics is preserved end-to-end.

use std::collections::BTreeSet;
use std::sync::Arc;

use wasmtime::component::{Resource, ResourceTable};

use covalence_pure as cp;

/// Backing type for `cov:pure/api.pure-type`.
pub struct HostPureType(pub cp::Type);

/// Backing type for `cov:pure/api.term`.
pub struct HostTerm(pub cp::Term);

/// Backing type for `cov:pure/api.term-set`.
///
/// Currently `Arc<BTreeSet<Term>>` — the WIT surface deliberately hides
/// this. Guests interact only via `len`/`is-empty`/`contains`/`at`,
/// so swapping in a persistent set or hash-trie later is invisible.
pub struct HostTermSet(pub Arc<BTreeSet<cp::Term>>);

impl HostTermSet {
    /// Indexed access in BTreeSet order. Guests must not depend on any
    /// particular total order — only on stability for this resource's
    /// lifetime.
    pub fn at(&self, idx: u32) -> Option<cp::Term> {
        self.0.iter().nth(idx as usize).cloned()
    }
}

/// Backing type for `cov:pure/api.thm`.
pub struct HostThm(pub cp::Thm);

// Resource keys in `with:` use dot (not slash) between interface and
// resource. `imports: { default: trappable }` makes WIT methods that
// return `result<T, string>` map to `wasmtime::Result<Result<T, String>>`.
wasmtime::component::bindgen!({
    path: "wit/pure.wit",
    world: "pure-guest",
    with: {
        "cov:pure/api.pure-type": HostPureType,
        "cov:pure/api.term": HostTerm,
        "cov:pure/api.term-set": HostTermSet,
        "cov:pure/api.thm": HostThm,
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

    fn push_type(&mut self, t: cp::Type) -> wasmtime::Result<Resource<HostPureType>> {
        self.table
            .push(HostPureType(t))
            .map_err(wasmtime::Error::from)
    }

    fn push_term(&mut self, t: cp::Term) -> wasmtime::Result<Resource<HostTerm>> {
        self.table.push(HostTerm(t)).map_err(wasmtime::Error::from)
    }

    fn push_thm(&mut self, t: cp::Thm) -> wasmtime::Result<Resource<HostThm>> {
        self.table.push(HostThm(t)).map_err(wasmtime::Error::from)
    }

    fn push_term_set(
        &mut self,
        t: Arc<BTreeSet<cp::Term>>,
    ) -> wasmtime::Result<Resource<HostTermSet>> {
        self.table
            .push(HostTermSet(t))
            .map_err(wasmtime::Error::from)
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

fn err_str(e: cp::Error) -> String {
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
    fn tfree(&mut self, name: String) -> wasmtime::Result<Resource<HostPureType>> {
        self.push_type(cp::Type::tfree(&name))
    }

    fn prop(&mut self) -> wasmtime::Result<Resource<HostPureType>> {
        self.push_type(cp::Type::prop())
    }

    fn bytes(&mut self) -> wasmtime::Result<Resource<HostPureType>> {
        self.push_type(cp::Type::bytes())
    }

    fn fun(
        &mut self,
        dom: Resource<HostPureType>,
        cod: Resource<HostPureType>,
    ) -> wasmtime::Result<Resource<HostPureType>> {
        let d = self.table.get(&dom)?.0.clone();
        let c = self.table.get(&cod)?.0.clone();
        self.push_type(cp::Type::fun(d, c))
    }

    fn tycon(
        &mut self,
        name: String,
        args: Vec<Resource<HostPureType>>,
    ) -> wasmtime::Result<Resource<HostPureType>> {
        let mut v = Vec::with_capacity(args.len());
        for r in &args {
            v.push(self.table.get(r)?.0.clone());
        }
        self.push_type(cp::Type::tycon(&name, v))
    }

    fn equals(
        &mut self,
        this: Resource<HostPureType>,
        other: Resource<HostPureType>,
    ) -> wasmtime::Result<bool> {
        let a = self.table.get(&this)?;
        let b = self.table.get(&other)?;
        Ok(a.0 == b.0)
    }

    fn is_prop(&mut self, this: Resource<HostPureType>) -> wasmtime::Result<bool> {
        Ok(self.table.get(&this)?.0.is_prop())
    }

    fn render(&mut self, this: Resource<HostPureType>) -> wasmtime::Result<String> {
        Ok(format!("{}", self.table.get(&this)?.0))
    }

    fn drop(&mut self, rep: Resource<HostPureType>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}

// ============================================================================
// term
// ============================================================================

impl cov::pure::api::HostTerm for PureHost {
    fn bound(&mut self, idx: u32) -> wasmtime::Result<Resource<HostTerm>> {
        self.push_term(cp::Term::bound(idx))
    }

    fn free(
        &mut self,
        name: String,
        ty: Resource<HostPureType>,
    ) -> wasmtime::Result<Resource<HostTerm>> {
        let ty = self.table.get(&ty)?.0.clone();
        self.push_term(cp::Term::free(&name, ty))
    }

    fn mk_const(
        &mut self,
        name: String,
        ty: Resource<HostPureType>,
    ) -> wasmtime::Result<Resource<HostTerm>> {
        let ty = self.table.get(&ty)?.0.clone();
        self.push_term(cp::Term::const_(&name, ty))
    }

    fn app(
        &mut self,
        fun: Resource<HostTerm>,
        arg: Resource<HostTerm>,
    ) -> wasmtime::Result<Resource<HostTerm>> {
        let f = self.table.get(&fun)?.0.clone();
        let a = self.table.get(&arg)?.0.clone();
        self.push_term(cp::Term::app(f, a))
    }

    fn abs(
        &mut self,
        hint: String,
        ty: Resource<HostPureType>,
        body: Resource<HostTerm>,
    ) -> wasmtime::Result<Resource<HostTerm>> {
        let ty = self.table.get(&ty)?.0.clone();
        let body = self.table.get(&body)?.0.clone();
        self.push_term(cp::Term::abs(&hint, ty, body))
    }

    fn imp(
        &mut self,
        lhs: Resource<HostTerm>,
        rhs: Resource<HostTerm>,
    ) -> wasmtime::Result<Resource<HostTerm>> {
        let l = self.table.get(&lhs)?.0.clone();
        let r = self.table.get(&rhs)?.0.clone();
        self.push_term(cp::Term::imp(l, r))
    }

    fn all(
        &mut self,
        hint: String,
        ty: Resource<HostPureType>,
        body: Resource<HostTerm>,
    ) -> wasmtime::Result<Resource<HostTerm>> {
        let ty = self.table.get(&ty)?.0.clone();
        let body = self.table.get(&body)?.0.clone();
        self.push_term(cp::Term::all(&hint, ty, body))
    }

    fn mk_eq(
        &mut self,
        lhs: Resource<HostTerm>,
        rhs: Resource<HostTerm>,
    ) -> wasmtime::Result<Resource<HostTerm>> {
        let l = self.table.get(&lhs)?.0.clone();
        let r = self.table.get(&rhs)?.0.clone();
        self.push_term(cp::Term::eq(l, r))
    }

    fn blob(&mut self, bytes: Vec<u8>) -> wasmtime::Result<Resource<HostTerm>> {
        // `Vec<u8>` -> `bytes::Bytes` is the zero-copy `From` impl in `bytes`.
        self.push_term(cp::Term::blob(bytes))
    }

    fn type_of(&mut self, this: Resource<HostTerm>) -> Trappable<Resource<HostPureType>> {
        let t = self.table.get(&this)?.0.clone();
        match t.type_of() {
            Ok(ty) => Ok(Ok(self.push_type(ty)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn equals(
        &mut self,
        this: Resource<HostTerm>,
        other: Resource<HostTerm>,
    ) -> wasmtime::Result<bool> {
        let a = self.table.get(&this)?;
        let b = self.table.get(&other)?;
        Ok(a.0 == b.0)
    }

    fn has_no_obs(&mut self, this: Resource<HostTerm>) -> wasmtime::Result<bool> {
        Ok(self.table.get(&this)?.0.has_no_obs())
    }

    fn render(&mut self, this: Resource<HostTerm>) -> wasmtime::Result<String> {
        Ok(format!("{}", self.table.get(&this)?.0))
    }

    fn drop(&mut self, rep: Resource<HostTerm>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}

// ============================================================================
// term-set
// ============================================================================

impl cov::pure::api::HostTermSet for PureHost {
    fn len(&mut self, this: Resource<HostTermSet>) -> wasmtime::Result<u32> {
        Ok(self.table.get(&this)?.0.len() as u32)
    }

    fn is_empty(&mut self, this: Resource<HostTermSet>) -> wasmtime::Result<bool> {
        Ok(self.table.get(&this)?.0.is_empty())
    }

    fn contains(
        &mut self,
        this: Resource<HostTermSet>,
        t: Resource<HostTerm>,
    ) -> wasmtime::Result<bool> {
        let needle = self.table.get(&t)?.0.clone();
        Ok(self.table.get(&this)?.0.contains(&needle))
    }

    fn at(
        &mut self,
        this: Resource<HostTermSet>,
        idx: u32,
    ) -> wasmtime::Result<Option<Resource<HostTerm>>> {
        let got = self.table.get(&this)?.at(idx);
        match got {
            Some(t) => Ok(Some(self.push_term(t)?)),
            None => Ok(None),
        }
    }

    fn drop(&mut self, rep: Resource<HostTermSet>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}

// ============================================================================
// thm
// ============================================================================

impl cov::pure::api::HostThm for PureHost {
    // ---- LF rules ----

    fn assume(&mut self, phi: Resource<HostTerm>) -> Trappable<Resource<HostThm>> {
        let phi = self.table.get(&phi)?.0.clone();
        match cp::Thm::assume(phi) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn imp_intro(
        &mut self,
        this: Resource<HostThm>,
        phi: Resource<HostTerm>,
    ) -> Trappable<Resource<HostThm>> {
        let thm = self.table.get(&this)?.0.clone();
        let phi = self.table.get(&phi)?.0.clone();
        match thm.imp_intro(&phi) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn imp_elim(
        &mut self,
        this: Resource<HostThm>,
        hyp: Resource<HostThm>,
    ) -> Trappable<Resource<HostThm>> {
        let thm = self.table.get(&this)?.0.clone();
        let hyp = self.table.get(&hyp)?.0.clone();
        match thm.imp_elim(hyp) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn all_intro(
        &mut self,
        this: Resource<HostThm>,
        name: String,
        ty: Resource<HostPureType>,
    ) -> Trappable<Resource<HostThm>> {
        let thm = self.table.get(&this)?.0.clone();
        let ty = self.table.get(&ty)?.0.clone();
        match thm.all_intro(&name, ty) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn all_elim(
        &mut self,
        this: Resource<HostThm>,
        witness: Resource<HostTerm>,
    ) -> Trappable<Resource<HostThm>> {
        let thm = self.table.get(&this)?.0.clone();
        let witness = self.table.get(&witness)?.0.clone();
        match thm.all_elim(witness) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    // ---- Equality rules ----

    fn refl(&mut self, t: Resource<HostTerm>) -> Trappable<Resource<HostThm>> {
        let t = self.table.get(&t)?.0.clone();
        match cp::Thm::refl(t) {
            Ok(th) => Ok(Ok(self.push_thm(th)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn trans(
        &mut self,
        this: Resource<HostThm>,
        other: Resource<HostThm>,
    ) -> Trappable<Resource<HostThm>> {
        let a = self.table.get(&this)?.0.clone();
        let b = self.table.get(&other)?.0.clone();
        match a.trans(b) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn sym(&mut self, this: Resource<HostThm>) -> Trappable<Resource<HostThm>> {
        let a = self.table.get(&this)?.0.clone();
        match a.sym() {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn cong_app(
        &mut self,
        this: Resource<HostThm>,
        arg: Resource<HostThm>,
    ) -> Trappable<Resource<HostThm>> {
        let a = self.table.get(&this)?.0.clone();
        let b = self.table.get(&arg)?.0.clone();
        match a.cong_app(b) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn cong_abs(
        &mut self,
        this: Resource<HostThm>,
        name: String,
        ty: Resource<HostPureType>,
    ) -> Trappable<Resource<HostThm>> {
        let a = self.table.get(&this)?.0.clone();
        let ty = self.table.get(&ty)?.0.clone();
        match a.cong_abs(&name, ty) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn beta_conv(&mut self, app: Resource<HostTerm>) -> Trappable<Resource<HostThm>> {
        let a = self.table.get(&app)?.0.clone();
        match cp::Thm::beta_conv(a) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn eta_conv(&mut self, abs: Resource<HostTerm>) -> Trappable<Resource<HostThm>> {
        let a = self.table.get(&abs)?.0.clone();
        match cp::Thm::eta_conv(a) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    fn inst_tfree(
        &mut self,
        this: Resource<HostThm>,
        name: String,
        replacement: Resource<HostPureType>,
    ) -> Trappable<Resource<HostThm>> {
        let a = self.table.get(&this)?.0.clone();
        let r = self.table.get(&replacement)?.0.clone();
        match a.inst_tfree(&name, r) {
            Ok(t) => Ok(Ok(self.push_thm(t)?)),
            Err(e) => Ok(Err(err_str(e))),
        }
    }

    // ---- Accessors ----

    fn hyps(&mut self, this: Resource<HostThm>) -> wasmtime::Result<Resource<HostTermSet>> {
        // Cheap: `Thm` already stores hyps as `Arc<BTreeSet<Term>>`.
        let hyps = self.table.get(&this)?.0.hyps().clone();
        // `hyps()` returns &BTreeSet<Term> — wrap into Arc. We could
        // expose Arc-shared hyps if performance matters; clone is fine
        // for MVP.
        self.push_term_set(Arc::new(hyps))
    }

    fn concl(&mut self, this: Resource<HostThm>) -> wasmtime::Result<Resource<HostTerm>> {
        let c = self.table.get(&this)?.0.concl().clone();
        self.push_term(c)
    }

    fn has_no_obs(&mut self, this: Resource<HostThm>) -> wasmtime::Result<bool> {
        Ok(self.table.get(&this)?.0.has_no_obs())
    }

    fn render(&mut self, this: Resource<HostThm>) -> wasmtime::Result<String> {
        Ok(format!("{}", self.table.get(&this)?.0))
    }

    fn drop(&mut self, rep: Resource<HostThm>) -> wasmtime::Result<()> {
        self.table.delete(rep)?;
        Ok(())
    }
}
