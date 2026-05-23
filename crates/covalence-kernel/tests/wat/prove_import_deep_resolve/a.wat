(component
    (import "prove-{b_hex}" (instance $b))
    (core module $m (func $start) (start $start))
    (core instance $i (instantiate $m))
)
