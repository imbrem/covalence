; The high-level specification of the `option` type

(#tydecl
(option 'a #ty)
)

(#decl
(none : option 'a)
(some : 'a -> option 'a)
(case : option 'a -> 'b -> ('a -> 'b) -> 'b)
)

(#clause
(e => none) ; variables on the left of a rule are _universally_ quantified
(e => some a) ; variables on the right of a rule which do _not_ appear on the left are _existentially_ quantified
) ; a clause is a _disjunction_ of predicates, at least one of which must be true

(#clause
(case none b f => b)
)

(#clause
(case (some a) b f => f a)
)

; The types of questions we might want to ask about a given specification, for future reference

(spec a |- spec b)

(spec a |- unique (spec b))

(|- categoricity (spec a))
