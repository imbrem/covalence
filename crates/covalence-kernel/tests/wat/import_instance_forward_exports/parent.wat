(component
    (import "attest" (func $attest))
    (import "component-{dep_hex}" (instance $lib
        (export "add" (func (param "a" s32) (param "b" s32) (result s32)))
    ))
    (alias export $lib "add" (func $add))
    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "add" (func $add (param i32 i32) (result i32)))
        (func $start
            (drop (call $add (i32.const 1) (i32.const 2)))
            (call $attest)
        )
        (start $start)
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core func $add_lowered (canon lower (func $add)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "add" (func $add_lowered))
        ))
    ))
)
