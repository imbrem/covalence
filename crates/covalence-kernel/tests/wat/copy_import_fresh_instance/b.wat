;; Imports D as a copy (fresh instance), exports go = D.inc.
(component
    (import "copy-{d_hex}" (instance $d
        (export "inc" (func (result s32)))
    ))
    (alias export $d "inc" (func $d_inc))
    (core module $m
        (import "env" "d-inc" (func $d_inc (result i32)))
        (func $go (result i32) (call $d_inc))
        (export "go" (func $go))
    )
    (core func $d_inc_lowered (canon lower (func $d_inc)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "d-inc" (func $d_inc_lowered))
        ))
    ))
    (func $go (result s32) (canon lift (core func $i "go")))
    (export "go" (func $go))
)
