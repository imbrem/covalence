(component
    (import "prove-{dep_hex}" (instance $lib
        (export "noop" (func))
    ))
    (alias export $lib "noop" (func $noop))
    (core module $m
        (import "env" "noop" (func $noop))
        (func $start (call $noop))
        (start $start)
    )
    (core func $noop_lowered (canon lower (func $noop)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "noop" (func $noop_lowered))
        ))
    ))
)
