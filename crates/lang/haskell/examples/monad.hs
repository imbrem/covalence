-- A monad-ish example in the dialect: the reader/environment monad, encoded
-- as plain functions `env -> a`. Exercises `if`/`then`/`else`, tuples, and
-- list literals alongside the combinators.

-- return :: a -> (env -> a)
ret :: a -> env -> a
ret x e = x

-- bind :: (env -> a) -> (a -> env -> b) -> (env -> b)
bind :: (env -> a) -> (a -> env -> b) -> env -> b
bind m k e = k (m e) e

-- ask :: env -> env
ask :: env -> env
ask e = e

-- A computation that reads the environment and branches on a predicate,
-- returning a tagged tuple either way.
classify :: (env -> Bool) -> env -> Pair
classify p = bind ask (\e -> ret (if p e then (tagHi, e) else (tagLo, e)))

-- A small program: sequence two reads into a two-element list.
pair2 :: env -> List
pair2 = bind ask (\x -> bind ask (\y -> ret [x, y]))
