(component
    (import "prove-{a_hex}" (instance $a))
    (core module $m (func $start) (start $start))
    (core instance $i (instantiate $m))
)
