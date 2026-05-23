(component
    (import "attest" (func $attest))
    (core module $m
        (import "env" "attest" (func $attest))
        (func $go (call $attest))
        (export "go" (func $go))
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
        ))
    ))
    (func $go (canon lift (core func $i "go")))
    (export "go" (func $go))
)
