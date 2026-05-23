;; Imports D as a copy (fresh instance), exports run = D.inc.
;; (Distinct from b.wat so it gets a different hash.)
(component
    (import "copy-{d_hex}" (instance $d
        (export "inc" (func (result s32)))
    ))
    (alias export $d "inc" (func $d_inc))
    (core module $m
        (import "env" "d-inc" (func $d_inc (result i32)))
        (func $run (result i32) (call $d_inc))
        (export "run" (func $run))
    )
    (core func $d_inc_lowered (canon lower (func $d_inc)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "d-inc" (func $d_inc_lowered))
        ))
    ))
    (func $run (result s32) (canon lift (core func $i "run")))
    (export "run" (func $run))
)
