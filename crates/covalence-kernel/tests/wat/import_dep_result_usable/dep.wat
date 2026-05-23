(component
    (core module $m
        (func $get_val (result i32) (i32.const 42))
        (export "get-val" (func $get_val))
    )
    (core instance $i (instantiate $m))
    (func $get_val (result s32)
        (canon lift (core func $i "get-val"))
    )
    (export "get-val" (func $get_val))
)
