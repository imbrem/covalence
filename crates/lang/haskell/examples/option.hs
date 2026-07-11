-- A Church/eliminator-encoded Option, plus list helpers, in the dialect.
--
-- `none`/`some` are eliminators: `m d f` inspects the option `m`, using `d`
-- for none and `f x` for `some x`. That lets `mapOption` / `getOrElse` avoid
-- pattern matching, which the dialect does not (yet) have.

none :: r -> (a -> r) -> r
none d f = d

some :: a -> r -> (a -> r) -> r
some x d f = f x

mapOption :: (a -> b) -> Option a -> Option b
mapOption g m = m none (compose some g)

getOrElse :: a -> Option a -> a
getOrElse d m = m d (\x -> x)

isSome :: Option a -> Bool
isSome m = m false (\x -> true)

-- A tiny list built from the eliminator-encoded pair/nil, plus a fold.
nil :: r -> (a -> l -> r) -> r
nil n c = n

cons :: a -> l -> r -> (a -> l -> r) -> r
cons h t n c = c h t

singleton :: a -> l
singleton x = cons x nil
