(component
    (import "attest" (func $attest))
    (core module $m
        (import "env" "attest" (func $attest))
        (func $start (call $attest))
        (start $start)
        (func $val (result i32) (i32.const 42))
        (export "val" (func $val))
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
        ))
    ))
    (func $val (result s32) (canon lift (core func $i "val")))
    (export "val" (func $val))
)
