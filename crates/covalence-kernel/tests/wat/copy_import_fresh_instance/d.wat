;; Counter component: inc returns the old value, then increments.
(component
    (core module $m
        (global $counter (mut i32) (i32.const 0))
        (func $inc (result i32)
            (local $old i32)
            (local.set $old (global.get $counter))
            (global.set $counter (i32.add (global.get $counter) (i32.const 1)))
            (local.get $old)
        )
        (export "inc" (func $inc))
    )
    (core instance $i (instantiate $m))
    (func $inc (result s32) (canon lift (core func $i "inc")))
    (export "inc" (func $inc))
)
