(component
    (import "attest" (func $attest))
    (import "component-{c_hex}" (instance $c
        (export "inc" (func (result s32)))
    ))
    (import "prove-{b_hex}" (instance $b
        (export "go" (func (result s32)))
    ))
    (alias export $c "inc" (func $c_inc))
    (alias export $b "go" (func $b_go))
    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "c-inc" (func $c_inc (result i32)))
        (import "env" "b-go" (func $b_go (result i32)))
        (func $start
            (drop (call $c_inc))
            (drop (call $b_go))
            (drop (i32.div_u
                (i32.const 1)
                (i32.eqz (i32.sub (call $c_inc) (i32.const 1)))
            ))
            (call $attest)
        )
        (start $start)
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core func $c_inc_lowered (canon lower (func $c_inc)))
    (core func $b_go_lowered (canon lower (func $b_go)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "c-inc" (func $c_inc_lowered))
            (export "b-go" (func $b_go_lowered))
        ))
    ))
)
