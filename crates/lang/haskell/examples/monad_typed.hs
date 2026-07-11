-- The ABSTRACT monad, in the plain-HOL shape of
-- `crates/kernel/hol/init/src/init/monad.rs`, written in the dialect and
-- lowered THROUGH the covalence-hol-api traits into real HOL terms
-- (tests/typed_monad.rs).
--
-- A monad is modelled by two operations over a carrier type variable `mcar`
-- and element type variable `a`:
--
--   ret  :: a -> mcar               (return / unit)
--   bind :: mcar -> (a -> mcar) -> mcar   (>>=)
--
-- These are FREE VARIABLES of the theory (an ambient environment seeds them in
-- the typed backend), exactly as in monad.rs. `map` is DEFINED from them, and
-- `mapKernel f` is the `\y -> ret (f y)` continuation `map` binds with.
--
-- The carrier `mcar` is a plain HOL type variable — standard HOL has no
-- type-constructor variables — so the abstraction is single-typed (`ret`,
-- `bind`, `map` all live over one carrier). This mirrors monad.rs's
-- `Type::tfree("mcar")` / `Type::tfree("a")`.

-- `\y -> ret (f y)` — the map kernel, for `f :: a -> a`.
mapKernel :: (a -> a) -> a -> mcar
mapKernel f = \(y :: a) -> ret (f y)

-- `map f x = bind x (\y -> ret (f y))` — the monadic map built from ret/bind.
-- Lowers to `\f. \x. bind x (\y. ret (f y))`, matching monad.rs's `map_op`.
map :: (a -> a) -> mcar -> mcar
map f x = bind x (\(y :: a) -> ret (f y))
