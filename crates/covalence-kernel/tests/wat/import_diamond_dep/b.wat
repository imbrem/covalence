(component
    (import "link-{d_hex}" (instance $d))
    (core module $m
        (func $val (result i32) (i32.const 1))
        (export "val" (func $val))
    )
    (core instance $i (instantiate $m))
    (func $val (result s32) (canon lift (core func $i "val")))
    (export "val" (func $val))
)
