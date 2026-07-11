-- Core combinators, written in the covalence Haskell dialect.
-- Type signatures are accepted and ignored (the dialect is untyped for now).

id :: a -> a
id x = x

const :: a -> b -> a
const x y = x

compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

apply :: (a -> b) -> a -> b
apply f x = f x
