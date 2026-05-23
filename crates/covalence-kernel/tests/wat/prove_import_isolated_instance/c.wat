(component
    (core module $m
        (global $ctr (mut i32) (i32.const 0))
        (func $inc (result i32)
            (global.get $ctr)
            (global.set $ctr (i32.add (global.get $ctr) (i32.const 1)))
        )
        (export "inc" (func $inc))
    )
    (core instance $i (instantiate $m))
    (func $inc (result s32) (canon lift (core func $i "inc")))
    (export "inc" (func $inc))
)
