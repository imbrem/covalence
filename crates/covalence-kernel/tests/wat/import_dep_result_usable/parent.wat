(component
    (import "attest" (func $attest))
    (import "component-{dep_hex}" (instance $lib
        (export "get-val" (func (result s32)))
    ))
    (alias export $lib "get-val" (func $get_val))
    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "get-val" (func $get_val (result i32)))
        (func $start
            (if (i32.eq (call $get_val) (i32.const 42))
                (then (call $attest))
            )
        )
        (start $start)
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core func $get_val_lowered (canon lower (func $get_val)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "get-val" (func $get_val_lowered))
        ))
    ))
)
