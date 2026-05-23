(component
    (import "component-{shared_hex}" (instance $shared
        (export "val" (func (result s32)))
    ))
    (core module $m
        (func $noop)
        (export "noop" (func $noop))
    )
    (core instance $i (instantiate $m))
    (func $noop (canon lift (core func $i "noop")))
    (export "noop" (func $noop))
)
