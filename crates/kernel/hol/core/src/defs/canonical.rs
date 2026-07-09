//! The kernel's canonical symbol catalogue.
//!
//! [`Canonical`] is a non-exhaustive enum naming every type-spec or
//! term-spec the kernel ships out of the box. New variants land as
//! the derived-types catalogue grows (see `notes/vibes/type-hierarchy.md`).

use super::symbol::{Symbol, TrustedCmp, sealed};
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
    // (on `bool` literals) reduced by the certificate path — exactly
    // like the arithmetic ops. `T`/`F` stay `TermKind::Bool` literals.
    /// `T := (λp:bool. p) = (λp:bool. p)` — truth as a **defined
    /// constant** (HOL Light `T_DEF`). Coexists with the transitional
    /// `TermKind::Bool(true)` literal until the literal-leaf endgame
    /// (EG5); the two are bridged by a *derived* eval-tier theorem
    /// (`covalence-hol-eval::derived`), never an admitted rule.
    True,
    /// `F := ∀p:bool. p` — falsity as a **defined constant** (HOL Light
    /// `F_DEF`). Same coexistence story as [`Canonical::True`].
    False,
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

    /// `fail : 'a := ε(λx. T)` — the unspecified inhabitant of any
    /// type; the result of partial ops on their "no answer" branch.
    Fail,

    // ---- Function combinators (point-free utilities) ----
    /// `fun.id : 'a → 'a` ≡ `λx. x`.
    Id,
    /// `fun.const : 'a → 'b → 'a` ≡ `λx _. x`.
    Const,
    /// `fun.compose : ('b → 'c) → ('a → 'b) → 'a → 'c` ≡ `λg f x. g (f x)`.
    Compose,
    /// `fun.flip : ('a → 'b → 'c) → 'b → 'a → 'c` ≡ `λf y x. f x y`.
    Flip,

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

    // ---- Bit strings and fixed-width unsigned integers ----
    /// `bits := list bool` — variable-length bit strings.
    Bits,
    /// `bits.len : bits → nat` — bit-string length (`list.length` of
    /// the underlying `list bool`).
    BitsLen,
    /// `u1 (bit) := { v : bits | bits.len v = 1 }`.
    Bit,
    /// `u2 := { v : bits | bits.len v = 2 }` (crumb).
    U2,
    /// `u4 := { v : bits | bits.len v = 4 }` (nybble).
    U4,
    /// `u8 := { v : bits | bits.len v = 8 }` (byte).
    U8,
    /// `u16 := { v : bits | bits.len v = 16 }`.
    U16,
    /// `u32 := { v : bits | bits.len v = 32 }` (word).
    U32,
    /// `u64 := { v : bits | bits.len v = 64 }` (dword).
    U64,
    /// `u128 := { v : bits | bits.len v = 128 }` (qword).
    U128,
    /// `u256 := { v : bits | bits.len v = 256 }` (yword).
    U256,
    /// `u512 := { v : bits | bits.len v = 512 }` (zword).
    U512,
    /// Signed fixed-width integers, thin typedefs over the unsigned
    /// `uN` of the same width (matching the WebAssembly component
    /// model's `s8`…`s64`; `s1`…`s4`/`s128`…`s512` round out the set).
    /// `sN := uN` — same bit representation, distinct type.
    S1,
    S2,
    S4,
    S8,
    S16,
    S32,
    S64,
    S128,
    S256,
    S512,
    /// `fin n := coprod (fin (n-1)) unit` (fixed-size finite type).
    Fin,

    // ---- Text: characters and strings ----
    /// `char := { c : nat | c < 0x110000 }` — a Unicode *codepoint*: a
    /// `nat` carved down to the Unicode codepoint range `0 ..= 0x10FFFF`.
    /// The bound `< 0x110000` is contiguous and includes the UTF-16
    /// surrogate gap `0xD800 ..= 0xDFFF` (a strict *scalar value* would
    /// exclude it; the contiguous range is the simplest correct carve and
    /// avoids a disjunction in the selector predicate — see
    /// `init/char.rs`).
    Char,
    /// `char.code : char → nat` — the codepoint of a character (the `rep`
    /// coercion `char → nat`, named).
    CharCode,
    /// `char.mk : nat → char` — the character with a given codepoint (the
    /// `abs` coercion `nat → char`, named; junk-saturating for
    /// out-of-range codepoints, as with any subtype `abs`).
    CharMk,
    /// `string := list char` — a string as a sequence of Unicode
    /// codepoints. A newtype over `list char`; UTF-8-as-bytes is a
    /// separate *encoding* concern (a `string ↔ bytes` codec) layered on
    /// top, not the logical model.
    String,

    // ---- Container types ----
    /// `option 'a := coprod 'a unit`.
    Option,
    /// `stream 'a := nat → 'a` (opaque TypeSpec wrapper; bridge to
    /// the carrier via `stream_at` / `stream_mk`).
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
    /// `int.pos := { x : int | 0 < x }` — strictly-positive integers
    /// (the denominator type for `rat`).
    IntPos,

    // ---- Rationals / reals / floats ----
    /// `fieldOfFractions[mul, zero] 'a := prod 'a 'a quot (standard)`.
    /// `rat := fieldOfFractions int`.
    Rat,
    /// `ratLe : rat → rat → bool` — the order relation on rationals.
    /// Declaration-only at the kernel level; postulated/derived
    /// downstream once `rat` has a concrete construction.
    RatLe,
    /// `f32 := u32` (bitwise). Will be re-axiomatised through `rat`
    /// once floating-point operations land. (The reals are not part of the
    /// kernel catalogue — they live in `covalence-hol::init::real`.)
    F32,
    /// `f64 := u64` (bitwise). Will be re-axiomatised through `rat`
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
    /// (`if b then x else y`). A let-style definition
    /// (`λt x y. ε z. (t = T ⟹ z = x) ∧ (t = F ⟹ z = y)`); the
    /// reduction rules `cond T x y = x` and `cond F x y = y` are
    /// *derived* downstream (`covalence-hol`'s `init::cond`) via the
    /// choice axiom. Construct applications with [`crate::Term::cond`].
    Cond,
    /// `option.isSome : option 'a → bool`. True for `some _`, false for
    /// `none`. Defined via `option.case`.
    IsSome,
    /// `option.unwrap : option 'a → 'a`. Extract the wrapped value if
    /// `some _`; the unspecified Hilbert-ε value for `none`. Defined
    /// via `option.case`.
    Unwrap,
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
    /// forms reduce via the certificate path.
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
    /// the certificate path.
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
    /// `set.mk : ('a → bool) → set 'a` — wrap a membership predicate
    /// into a set (the `abs` coercion, named). The constructor every
    /// other set op funnels through.
    SetMk,
    /// `set.mem : 'a → set 'a → bool` — membership (the `rep` coercion
    /// applied, named).
    SetMem,
    /// `set.empty : set 'a` — the empty set `mk (λx. F)`.
    SetEmpty,
    /// `set.singleton : 'a → set 'a` — `λa. mk (λx. x = a)`.
    SetSingleton,
    /// `set.insert : 'a → set 'a → set 'a` — add an element,
    /// `λa s. mk (λx. x = a ∨ mem x s)`.
    SetInsert,
    /// `set.union : set 'a → set 'a → set 'a`.
    SetUnion,
    /// `set.intersect : set 'a → set 'a → set 'a`.
    SetIntersect,
    /// `set.diff : set 'a → set 'a → set 'a`.
    SetDiff,
    /// `set.subset : set 'a → set 'a → bool`.
    SetSubset,
    /// `set.isEmpty : set 'a → bool` — `λs. ∀x. ¬ mem x s`.
    SetIsEmpty,
    /// `set.flatten : set (set 'a) → set 'a` — union of a set of sets.
    SetFlatten,
    /// `set.all : set bool → bool` — `T` iff every member is `T`
    /// (big conjunction over the set).
    SetAll,
    /// `set.any : set bool → bool` — `T` iff some member is `T`
    /// (big disjunction over the set).
    SetAny,
    /// `set.finite : set 'a → bool` — `λs. ∃l:list 'a. list.elems l = s`
    /// (Kuratowski-finite: the set is the element-set of some list).
    SetFinite,
    /// `set.card : set 'a → nat` — cardinality (the minimal length of a
    /// list whose `elems` is the set; junk on infinite sets).
    SetCard,
    /// `set.card? : set 'a → option nat` — cardinality as an option,
    /// `none` for infinite sets, `some (card s)` when finite.
    SetCardOpt,
    /// `set.min : set nat → nat` — least element (`0` for the empty
    /// set, by convention). Total by well-ordering of `nat`.
    SetMin,
    /// `set.image : ('a → 'b) → set 'a → set 'b` — direct image
    /// `λf s. mk (λy. ∃x. mem x s ∧ f x = y)`.
    SetImage,
    /// `set.preimage : ('a → 'b) → set 'b → set 'a` — preimage
    /// `λf t. mk (λx. mem (f x) t)`.
    SetPreimage,
    /// `list.elems : list 'a → set 'a` — the set of elements appearing
    /// in the list.
    ListElems,

    // ---- Term-level: relation operations ----
    /// `rel.mk : ('a → 'b → bool) → rel 'a 'b` — wrap a two-place
    /// predicate into a relation (the `abs` coercion, named).
    RelMk,
    /// `rel.holds : rel 'a 'b → 'a → 'b → bool` — does the relation
    /// relate the two arguments (the `rep` coercion applied, named).
    RelHolds,
    /// `rel.id : rel 'a 'a` ≡ `mk (λx y. x = y)` — the identity
    /// (equality) relation.
    RelId,
    /// `rel.compose : rel 'b 'c → rel 'a 'b → rel 'a 'c` ≡
    /// `λs r. mk (λx z. ∃y. holds r x y ∧ holds s y z)` — relational
    /// composition `s ∘ r`.
    RelCompose,
    /// `rel.converse : rel 'a 'b → rel 'b 'a` ≡
    /// `λr. mk (λy x. holds r x y)` — the converse relation.
    RelConverse,
    /// `rel.deterministic : rel 'a 'b → bool` ≡
    /// `λr. ∀x y y'. holds r x y ⟹ holds r x y' ⟹ y = y'` —
    /// single-valuedness (at most one image per input).
    RelDeterministic,
    /// `rel.total : rel 'a 'b → bool` ≡ `λr. ∀x. ∃y. holds r x y` —
    /// totality (at least one image per input).
    RelTotal,
    /// `rel.isFunction : rel 'a 'b → bool` ≡
    /// `λr. deterministic r ∧ total r` — the relation is the graph of a
    /// total function.
    RelIsFunction,
    /// `rel.toFun : rel 'a 'b → ('a → 'b)` ≡
    /// `λr x. ε y. holds r x y` — pick a function respecting the
    /// relation (the function when `isFunction r`, ε-junk otherwise).
    RelToFun,
    /// `rel.graph : ('a → 'b) → rel 'a 'b` ≡ `λf. mk (λx y. f x = y)` —
    /// the graph of a function as a relation.
    RelGraph,

    // ---- Term-level: stream operations ----
    /// `streamAt : stream 'a → nat → 'a` — the bridge from opaque
    /// `stream α` back to its carrier function (apply at index).
    /// Defined as the newtype `rep` coercion.
    StreamAt,
    /// `streamMk : (nat → 'a) → stream 'a` — the bridge from a
    /// `nat → α` function to the opaque `stream α`. Inverse of
    /// `streamAt` under η. Defined as the newtype `abs` coercion.
    StreamMk,
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
            Canonical::True => "bool.true",
            Canonical::False => "bool.false",
            Canonical::And => "bool.and",
            Canonical::Or => "bool.or",
            Canonical::Not => "bool.not",
            Canonical::Imp => "bool.imp",
            Canonical::Iff => "bool.iff",
            Canonical::Forall => "bool.forall",
            Canonical::Exists => "bool.exists",
            Canonical::Fail => "fail",
            Canonical::Id => "fun.id",
            Canonical::Const => "fun.const",
            Canonical::Compose => "fun.compose",
            Canonical::Flip => "fun.flip",
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
            Canonical::Bits => "bits",
            Canonical::BitsLen => "bits.len",
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
            Canonical::S1 => "s1",
            Canonical::S2 => "s2",
            Canonical::S4 => "s4",
            Canonical::S8 => "s8",
            Canonical::S16 => "s16",
            Canonical::S32 => "s32",
            Canonical::S64 => "s64",
            Canonical::S128 => "s128",
            Canonical::S256 => "s256",
            Canonical::S512 => "s512",
            Canonical::Fin => "fin",
            Canonical::Char => "char",
            Canonical::CharCode => "char.code",
            Canonical::CharMk => "char.mk",
            Canonical::String => "string",
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
            Canonical::IntPos => "int.pos",
            Canonical::Rat => "rat",
            Canonical::RatLe => "rat.le",
            Canonical::F32 => "f32",
            Canonical::F64 => "f64",
            Canonical::None => "option.none",
            Canonical::Some => "option.some",
            Canonical::Ok => "result.ok",
            Canonical::Err => "result.err",
            Canonical::Cond => "bool.cond",
            Canonical::IsSome => "option.isSome",
            Canonical::Unwrap => "option.unwrap",
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
            Canonical::SetMk => "set.mk",
            Canonical::SetMem => "set.mem",
            Canonical::SetEmpty => "set.empty",
            Canonical::SetSingleton => "set.singleton",
            Canonical::SetInsert => "set.insert",
            Canonical::SetUnion => "set.union",
            Canonical::SetIntersect => "set.intersect",
            Canonical::SetDiff => "set.diff",
            Canonical::SetSubset => "set.subset",
            Canonical::SetIsEmpty => "set.isEmpty",
            Canonical::SetFlatten => "set.flatten",
            Canonical::SetAll => "set.all",
            Canonical::SetAny => "set.any",
            Canonical::SetFinite => "set.finite",
            Canonical::SetCard => "set.card",
            Canonical::SetCardOpt => "set.card?",
            Canonical::SetMin => "set.min",
            Canonical::SetImage => "set.image",
            Canonical::SetPreimage => "set.preimage",
            Canonical::ListElems => "list.elems",
            Canonical::RelMk => "rel.mk",
            Canonical::RelHolds => "rel.holds",
            Canonical::RelId => "rel.id",
            Canonical::RelCompose => "rel.compose",
            Canonical::RelConverse => "rel.converse",
            Canonical::RelDeterministic => "rel.deterministic",
            Canonical::RelTotal => "rel.total",
            Canonical::RelIsFunction => "rel.isFunction",
            Canonical::RelToFun => "rel.toFun",
            Canonical::RelGraph => "rel.graph",
            Canonical::Stream => "stream",
            Canonical::StreamAt => "stream.at",
            Canonical::StreamMk => "stream.mk",
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

// The kernel's own catalogue names are trusted: each variant has a
// unique, stable `label()`, so label comparison is a faithful identity.
impl sealed::Sealed for Canonical {}
impl TrustedCmp for Canonical {}
