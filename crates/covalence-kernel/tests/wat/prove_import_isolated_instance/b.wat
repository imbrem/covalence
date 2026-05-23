(component
    (import "component-{c_hex}" (instance $c
        (export "inc" (func (result s32)))
    ))
    (alias export $c "inc" (func $c_inc))
    (core module $m
        (import "env" "c-inc" (func $c_inc (result i32)))
        (func $go (result i32) (call $c_inc))
        (export "go" (func $go))
    )
    (core func $c_inc_lowered (canon lower (func $c_inc)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "c-inc" (func $c_inc_lowered))
        ))
    ))
    (func $go (result s32) (canon lift (core func $i "go")))
    (export "go" (func $go))
)
