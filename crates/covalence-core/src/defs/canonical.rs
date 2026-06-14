//! The kernel's canonical symbol catalogue.
//!
//! [`Canonical`] is a non-exhaustive enum naming every type-spec or
//! term-spec the kernel ships out of the box. New variants land as
//! the derived-types catalogue grows (see `docs/type-hierarchy.md`).

use super::symbol::Symbol;
use std::fmt;

/// Names for the kernel's derived-type / derived-term catalogue.
///
/// The `#[non_exhaustive]` attribute lets us add new variants
/// without breaking downstream `match` users.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Canonical {
    // ---- Logical connectives (defined over `=` / `ε` + bool literals) ----
    //
    // `=` (`TermKind::Eq`) and `ε` (`TermKind::Select`) are the only
    // logical *primitives*; every connective below is an ordinary
    // let-style definition, unfolded by `Thm::unfold_term_spec` and
    // (on `bool` literals) reduced by `Thm::reduce_prim` — exactly
    // like the arithmetic ops. `T`/`F` stay `TermKind::Bool` literals.
    /// `(/\) := λp q. (λf. f p q) = (λf. f T T)`.
    And,
    /// `(\/) := λp q. !r. (p ==> r) ==> (q ==> r) ==> r`.
    Or,
    /// `(~) := λp. p ==> F`.
    Not,
    /// `(==>) := λp q. (p /\ q) = p`.
    Imp,
    /// `(<=>) := λp q. p = q` (bool equality).
    Iff,
    /// `(!) := λP. P = (λx. T)`.
    Forall,
    /// `(?) := λP. !q. (!x. P x ==> q) ==> q`.
    Exists,

    // ---- Singleton ----
    /// `unit := { b : bool | b = T }` — the one-element type. Defined
    /// in `defs/unit.rs` as a bool-subtype (was a builtin
    /// `TypeKind::Unit` before the migration). Its singleton property
    /// — any two inhabitants are equal — is the kernel rule
    /// [`crate::Thm::unit_eq`].
    Unit,
    /// `unit.nil : unit` — the canonical inhabitant of `unit`, defined
    /// as `abs T`. By [`crate::Thm::unit_eq`] it equals every other
    /// element of `unit`.
    UnitNil,

    // ---- Relational/algebraic primitives ----
    /// `set 'a := 'a → bool`.
    Set,
    /// `rel 'a 'b := 'a → 'b → bool`.
    Rel,
    /// `preord 'a := rel 'a 'a where (trans, refl)`.
    Preord,
    /// `pord 'a := rel 'a 'a where (trans, refl, antisym)`.
    Pord,
    /// `per 'a := rel 'a 'a where (trans, sym)`.
    Per,
    /// `part 'a := rel 'a 'a where (trans, sym, refl)`.
    Part,

    // ---- Product / coproduct ----
    /// `coprod 'a 'b := rel 'a 'b where (\R. (∃a. R = λx _. x = a) ∨ (∃b. R = λ_ y. y = b))`.
    Coprod,
    /// `prod 'a 'b := rel 'a 'b where (\R. ∃a b. R = λx y. x = a ∧ y = b)`.
    Prod,
    /// `pair : 'a → 'b → prod 'a 'b` — the pairing constructor
    /// `λa b. abs (λx y. x = a ∧ y = b)`.
    Pair,
    /// `fst : prod 'a 'b → 'a` — first projection (`ε`-defined).
    Fst,
    /// `snd : prod 'a 'b → 'b` — second projection (`ε`-defined).
    Snd,
    /// `inl : 'a → coprod 'a 'b` — left injection `λa. abs (λx _. x = a)`.
    Inl,
    /// `inr : 'b → coprod 'a 'b` — right injection `λb. abs (λ_ y. y = b)`.
    Inr,
    /// `coprodCase : ('a → 'c) → ('b → 'c) → coprod 'a 'b → 'c` — the
    /// disjoint-union eliminator (`ε`-defined). `coprodCase f g (inl a)
    /// = f a` and `coprodCase f g (inr b) = g b`.
    CoprodCase,

    // ---- Fixed-width unsigned integers ----
    /// `u1 := coprod unit unit` (bit).
    Bit,
    /// `u2 := coprod bit bit` (crumb).
    U2,
    /// `u4 := coprod u2 u2` (nybble).
    U4,
    /// `u8 := coprod u4 u4` (byte).
    U8,
    /// `u16 := coprod u8 u8`.
    U16,
    /// `u32 := coprod u16 u16` (word).
    U32,
    /// `u64 := coprod u32 u32` (dword).
    U64,
    /// `u128 := coprod u64 u64` (qword).
    U128,
    /// `u256 := coprod u128 u128` (yword).
    U256,
    /// `u512 := coprod u256 u256` (zword).
    U512,
    /// `bits := list bool`.
    Bits,
    /// `fin n := coprod (fin (n-1)) unit` (fixed-size finite type).
    Fin,

    // ---- Container types ----
    /// `option 'a := coprod 'a unit`.
    Option,
    /// `stream 'a := nat → 'a` (opaque TypeSpec wrapper; bridge to
    /// the carrier via `stream_at` / `stream_make`).
    Stream,
    /// `list 'a := stream (option 'a) where finite 'a`.
    List,
    /// `result 'a 'b := coprod 'a 'b`.
    Result,

    // ---- Bytes / blobs ----
    /// `bytes := list u8` — the type of byte literals (`TermKind::Blob`).
    /// Was the kernel-primitive `TypeKind::Bytes` before the migration
    /// to spec-derived numerical/byte types.
    Bytes,
    /// `bytesCat : bytes → bytes → bytes` — concatenation.
    BytesCat,
    /// `bytesConsNat : nat → bytes → bytes` — cons a nat (mod 256).
    BytesConsNat,
    /// `bytesLen : bytes → nat` — length.
    BytesLen,
    /// `bytesAt : bytes → nat → nat` — byte at index (0 if OOB).
    BytesAt,
    /// `bytesSlice : bytes → nat → nat → bytes` — saturating slice.
    BytesSlice,

    // ---- Signed integers and beyond ----
    /// `signed1 'a := prod bit 'a` (a or −a).
    Signed1,
    /// `signed2 'a := prod bit 'a` (a or −(a+1)) — two's-complement-ish.
    Signed2,
    /// `int := (nat × nat) / ~` (Grothendieck) — the type of integer
    /// literals (`TermKind::Int`). Was the kernel-primitive
    /// `TypeKind::Int` before the migration to spec-derived types.
    Int,

    // ---- Rationals / reals / floats ----
    /// `fieldOfFractions[mul, zero] 'a := prod 'a 'a quot (standard)`.
    /// `rat := fieldOfFractions int`.
    Rat,
    /// `ratLe : rat → rat → bool` — the order relation on rationals.
    /// Declaration-only at the kernel level; postulated/derived
    /// downstream once `rat` has a concrete construction.
    RatLe,
    /// `real := { rat } close ratLe` — Dedekind cuts. The carrier is
    /// `rat → bool` (subsets of `rat`); the selector predicate says
    /// "closed under `ratLe` and non-empty" (an upper cut).
    Real,
    /// `f32 := u32` (bitwise). Will be re-axiomatised through `real`
    /// once floating-point operations land.
    F32,
    /// `f64 := u64` (bitwise). Will be re-axiomatised through `real`
    /// once floating-point operations land.
    F64,

    // ---- Term-level: option constructors ----
    /// `none : option 'a`.
    None,
    /// `some : 'a → option 'a`.
    Some,

    // ---- Term-level: result constructors ----
    /// `ok : 'a → result 'a 'b` — successful result.
    Ok,
    /// `err : 'b → result 'a 'b` — error result.
    Err,

    // ---- Term-level: bool / option fundamentals ----
    /// `cond : bool → 'a → 'a → 'a` — the Boolean conditional
    /// (`if b then x else y`). Declaration-only; reduction rules
    /// `cond T x y = x` and `cond F x y = y` are postulated /
    /// proved downstream.
    Cond,
    /// `isSome : option 'a → bool`. True for `some _`, false for
    /// `none`. Declaration-only.
    IsSome,
    /// `fromSome : option 'a → 'a`. Extract the wrapped value if
    /// `some _`; unspecified (Hilbert-ε at the model level) for
    /// `none`. Declaration-only.
    FromSome,
    /// `optionCase : 'b → ('a → 'b) → option 'a → 'b` — the
    /// option eliminator. `optionCase default f none = default`
    /// and `optionCase default f (some x) = f x`. Declaration-only.
    OptionCase,

    // ---- Term-level: list operations ----
    /// `nil : list 'a`.
    Nil,
    /// `cons : 'a → list 'a → list 'a`.
    Cons,
    /// `head : list 'a → option 'a`.
    Head,
    /// `tail : list 'a → list 'a`.
    Tail,

    // ---- Term-level: nat arithmetic ----
    /// `natSucc : nat → nat` — the constructor `λn. n + 1`. Closed
    /// forms reduce via `builtins::reduce_spec`.
    NatSucc,
    /// `natPred : nat → nat` — saturating predecessor (`0 - 1 = 0`).
    NatPred,
    /// `natRec : 'a → (nat → 'a → 'a) → nat → 'a` — primitive recursor.
    /// Selector predicate: the standard `r z f 0 = z` and
    /// `r z f (S n) = f n (r z f n)` equations.
    NatRec,
    /// `iter : nat → ('a → 'a) → 'a → 'a` — apply `f` to `a` `n`
    /// times. Defined as `λn f a. natRec a (λ_. f) n`.
    Iter,
    /// `natAdd : nat → nat → nat`.
    NatAdd,
    /// `natMul : nat → nat → nat`.
    NatMul,
    /// `natSub : nat → nat → nat` (saturating at zero).
    NatSub,
    /// `natDiv : nat → nat → nat` (Euclidean, n/0 = 0).
    NatDiv,
    /// `natMod : nat → nat → nat` (Euclidean, n%0 = 0).
    NatMod,
    /// `natPow : nat → nat → nat`.
    NatPow,
    /// `natLe : nat → nat → bool`.
    NatLe,
    /// `natLt : nat → nat → bool`.
    NatLt,
    /// `natToInt : nat → int`.
    NatToInt,
    /// `natShl : nat → nat → nat` — left shift by `n` (i.e. `* 2^n`).
    NatShl,
    /// `natShr : nat → nat → nat` — right shift by `n` (i.e. `/ 2^n`,
    /// truncating toward zero).
    NatShr,
    /// `natBitAnd : nat → nat → nat` — bitwise AND.
    NatBitAnd,
    /// `natBitOr : nat → nat → nat` — bitwise OR.
    NatBitOr,
    /// `natBitXor : nat → nat → nat` — bitwise XOR.
    NatBitXor,
    /// `natToBytesLe : nat → blob` — minimal little-endian byte encoding.
    NatToBytesLe,
    /// `natToBytesBe : nat → blob` — minimal big-endian byte encoding.
    NatToBytesBe,
    /// `natFromBytesLe : blob → nat` — decode little-endian.
    NatFromBytesLe,
    /// `natFromBytesBe : blob → nat` — decode big-endian.
    NatFromBytesBe,

    // ---- Term-level: int arithmetic ----
    /// `intSucc : int → int` — `λz. z + 1`. Closed forms reduce via
    /// `builtins::reduce_spec`.
    IntSucc,
    /// `intPred : int → int` — `λz. z − 1`.
    IntPred,
    /// `intAdd : int → int → int`.
    IntAdd,
    /// `intMul : int → int → int`.
    IntMul,
    /// `intSub : int → int → int`.
    IntSub,
    /// `intDiv : int → int → int` (Euclidean, n/0 = 0).
    IntDiv,
    /// `intMod : int → int → int` (Euclidean, n%0 = 0).
    IntMod,
    /// `intNeg : int → int` (unary minus).
    IntNeg,
    /// `intAbs : int → nat`.
    IntAbs,
    /// `intSgn : int → int` (−1, 0, or 1).
    IntSgn,
    /// `intLe : int → int → bool`.
    IntLe,
    /// `intLt : int → int → bool`.
    IntLt,

    // ---- Term-level: list operations ----
    /// `listLength : list 'a → nat`.
    ListLength,
    /// `listCat : list 'a → list 'a → list 'a`.
    ListCat,
    /// `listMap : ('a → 'b) → list 'a → list 'b`.
    ListMap,
    /// `listFilter : ('a → bool) → list 'a → list 'a`.
    ListFilter,
    /// `listFoldr : ('a → 'b → 'b) → 'b → list 'a → 'b`.
    ListFoldr,
    /// `listFoldl : ('b → 'a → 'b) → 'b → list 'a → 'b`.
    ListFoldl,
    /// `listTake : nat → list 'a → list 'a`.
    ListTake,
    /// `listSkip : nat → list 'a → list 'a`.
    ListSkip,
    /// `listIndex : nat → list 'a → option 'a`.
    ListIndex,
    /// `listRepeat : nat → 'a → list 'a`.
    ListRepeat,
    /// `listFlatten : list (list 'a) → list 'a`.
    ListFlatten,

    // ---- Term-level: set operations ----
    /// `setUnion : set 'a → set 'a → set 'a`.
    SetUnion,
    /// `setIntersect : set 'a → set 'a → set 'a`.
    SetIntersect,
    /// `setDiff : set 'a → set 'a → set 'a`.
    SetDiff,
    /// `setSubset : set 'a → set 'a → bool`.
    SetSubset,
    /// `setCard : set 'a → nat`.
    SetCard,
    /// `listToSet : list 'a → set 'a`.
    ListToSet,

    // ---- Term-level: stream operations ----
    /// `streamAt : stream 'a → nat → 'a` — the bridge from opaque
    /// `stream α` back to its carrier function (apply at index).
    /// Declaration-only.
    StreamAt,
    /// `streamMake : (nat → 'a) → stream 'a` — the bridge from a
    /// `nat → α` function to the opaque `stream α`. Inverse of
    /// `streamAt` under η. Declaration-only.
    StreamMake,
    /// `streamHead : stream 'a → 'a` — `λs. stream_at s 0`.
    StreamHead,
    /// `streamTail : stream 'a → stream 'a` — `λs n. s (succ n)`.
    StreamTail,
    /// `streamCons : 'a → stream 'a → stream 'a` — prepend an element.
    StreamCons,
    /// `streamConst : 'a → stream 'a` — `λx n. x` (the constant stream).
    StreamConst,
    /// `streamIterate : 'a → ('a → 'a) → stream 'a` —
    /// `λx f n. iter n f x`.
    StreamIterate,
    /// `streamNth : nat → stream 'a → 'a` — `λn s. s n`.
    StreamNth,
    /// `finite : stream (option 'a) → bool` — the predicate
    /// characterizing finite-list-shaped streams: `∃N. ∀n. nat_le N n
    /// ⟹ s n = none`. Used as the selector predicate for
    /// `list 'a := stream (option 'a) where finite`.
    Finite,
}

impl Canonical {
    /// Human-readable label used in `Display` output and S-exp
    /// serialisation.
    pub fn label(&self) -> &'static str {
        match self {
            Canonical::And => "/\\",
            Canonical::Or => "\\/",
            Canonical::Not => "~",
            Canonical::Imp => "==>",
            Canonical::Iff => "<=>",
            Canonical::Forall => "!",
            Canonical::Exists => "?",
            Canonical::Unit => "unit",
            Canonical::UnitNil => "unit.nil",
            Canonical::Set => "set",
            Canonical::Rel => "rel",
            Canonical::Preord => "preord",
            Canonical::Pord => "pord",
            Canonical::Per => "per",
            Canonical::Part => "part",
            Canonical::Coprod => "coprod",
            Canonical::Prod => "prod",
            Canonical::Pair => "prod.pair",
            Canonical::Fst => "prod.fst",
            Canonical::Snd => "prod.snd",
            Canonical::Inl => "coprod.inl",
            Canonical::Inr => "coprod.inr",
            Canonical::CoprodCase => "coprod.case",
            Canonical::Bit => "bit",
            Canonical::U2 => "u2",
            Canonical::U4 => "u4",
            Canonical::U8 => "u8",
            Canonical::U16 => "u16",
            Canonical::U32 => "u32",
            Canonical::U64 => "u64",
            Canonical::U128 => "u128",
            Canonical::U256 => "u256",
            Canonical::U512 => "u512",
            Canonical::Bits => "bits",
            Canonical::Fin => "fin",
            Canonical::Option => "option",
            Canonical::List => "list",
            Canonical::Result => "result",
            Canonical::Bytes => "bytes",
            Canonical::BytesCat => "bytes.cat",
            Canonical::BytesConsNat => "bytes.consNat",
            Canonical::BytesLen => "bytes.len",
            Canonical::BytesAt => "bytes.at",
            Canonical::BytesSlice => "bytes.slice",
            Canonical::Signed1 => "signed1",
            Canonical::Signed2 => "signed2",
            Canonical::Int => "int",
            Canonical::Rat => "rat",
            Canonical::RatLe => "rat.le",
            Canonical::Real => "real",
            Canonical::F32 => "f32",
            Canonical::F64 => "f64",
            Canonical::None => "option.none",
            Canonical::Some => "option.some",
            Canonical::Ok => "result.ok",
            Canonical::Err => "result.err",
            Canonical::Cond => "bool.cond",
            Canonical::IsSome => "option.isSome",
            Canonical::FromSome => "option.fromSome",
            Canonical::OptionCase => "option.case",
            Canonical::Nil => "list.nil",
            Canonical::Cons => "list.cons",
            Canonical::Head => "list.head",
            Canonical::Tail => "list.tail",
            Canonical::NatSucc => "nat.succ",
            Canonical::NatPred => "nat.pred",
            Canonical::NatRec => "nat.rec",
            Canonical::Iter => "nat.iter",
            Canonical::NatAdd => "nat.add",
            Canonical::NatMul => "nat.mul",
            Canonical::NatSub => "nat.sub",
            Canonical::NatDiv => "nat.div",
            Canonical::NatMod => "nat.mod",
            Canonical::NatPow => "nat.pow",
            Canonical::NatLe => "nat.le",
            Canonical::NatLt => "nat.lt",
            Canonical::NatToInt => "nat.toInt",
            Canonical::NatShl => "nat.shl",
            Canonical::NatShr => "nat.shr",
            Canonical::NatBitAnd => "nat.bitAnd",
            Canonical::NatBitOr => "nat.bitOr",
            Canonical::NatBitXor => "nat.bitXor",
            Canonical::NatToBytesLe => "nat.toBytesLe",
            Canonical::NatToBytesBe => "nat.toBytesBe",
            Canonical::NatFromBytesLe => "nat.fromBytesLe",
            Canonical::NatFromBytesBe => "nat.fromBytesBe",
            Canonical::IntSucc => "int.succ",
            Canonical::IntPred => "int.pred",
            Canonical::IntAdd => "int.add",
            Canonical::IntMul => "int.mul",
            Canonical::IntSub => "int.sub",
            Canonical::IntDiv => "int.div",
            Canonical::IntMod => "int.mod",
            Canonical::IntNeg => "int.neg",
            Canonical::IntAbs => "int.abs",
            Canonical::IntSgn => "int.sgn",
            Canonical::IntLe => "int.le",
            Canonical::IntLt => "int.lt",
            Canonical::ListLength => "list.length",
            Canonical::ListCat => "list.cat",
            Canonical::ListMap => "list.map",
            Canonical::ListFilter => "list.filter",
            Canonical::ListFoldr => "list.foldr",
            Canonical::ListFoldl => "list.foldl",
            Canonical::ListTake => "list.take",
            Canonical::ListSkip => "list.skip",
            Canonical::ListIndex => "list.index",
            Canonical::ListRepeat => "list.repeat",
            Canonical::ListFlatten => "list.flatten",
            Canonical::SetUnion => "set.union",
            Canonical::SetIntersect => "set.intersect",
            Canonical::SetDiff => "set.diff",
            Canonical::SetSubset => "set.subset",
            Canonical::SetCard => "set.card",
            Canonical::ListToSet => "list.toSet",
            Canonical::Stream => "stream",
            Canonical::StreamAt => "stream.at",
            Canonical::StreamMake => "stream.make",
            Canonical::StreamHead => "stream.head",
            Canonical::StreamTail => "stream.tail",
            Canonical::StreamCons => "stream.cons",
            Canonical::StreamConst => "stream.const",
            Canonical::StreamIterate => "stream.iterate",
            Canonical::StreamNth => "stream.nth",
            Canonical::Finite => "stream.finite",
        }
    }
}

impl fmt::Display for Canonical {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

impl Symbol for Canonical {
    fn label(&self) -> &str {
        Canonical::label(self)
    }
}
