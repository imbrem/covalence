(component
    (import "attest" (func $attest))
    (import "prove-{dep_hex}" (instance $lib
        (export "go" (func))
    ))
    (alias export $lib "go" (func $go))
    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "go" (func $go))
        (func $start
            (call $go)
            (call $attest)
        )
        (start $start)
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core func $go_lowered (canon lower (func $go)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "go" (func $go_lowered))
        ))
    ))
)
