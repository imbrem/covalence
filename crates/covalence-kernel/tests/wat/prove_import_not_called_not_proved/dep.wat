(component
    (import "attest" (func $attest))
    (core module $m
        (import "env" "attest" (func $attest))
        (func $start (call $attest))
        (start $start)
        (func $noop)
        (export "noop" (func $noop))
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
        ))
    ))
    (func $noop (canon lift (core func $i "noop")))
    (export "noop" (func $noop))
)
