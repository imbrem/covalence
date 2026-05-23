;; Parent links D (shared), B and C (each copy D internally).
;; Verifies 3 separate D instances: d.inc()=0, b.go()=0, c.run()=0, d.inc()=1.
(component
    (import "attest" (func $attest))
    (import "link-{d_hex}" (instance $d
        (export "inc" (func (result s32)))
    ))
    (import "link-{b_hex}" (instance $b
        (export "go" (func (result s32)))
    ))
    (import "link-{c_hex}" (instance $c
        (export "run" (func (result s32)))
    ))
    (alias export $d "inc" (func $d_inc))
    (alias export $b "go" (func $b_go))
    (alias export $c "run" (func $c_run))
    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "d-inc" (func $d_inc (result i32)))
        (import "env" "b-go" (func $b_go (result i32)))
        (import "env" "c-run" (func $c_run (result i32)))
        (func $start
            ;; Shared D: first call returns 0
            (if (i32.ne (call $d_inc) (i32.const 0)) (then (unreachable)))
            ;; B's copy of D: first call returns 0 (fresh instance)
            (if (i32.ne (call $b_go) (i32.const 0)) (then (unreachable)))
            ;; C's copy of D: first call returns 0 (fresh instance)
            (if (i32.ne (call $c_run) (i32.const 0)) (then (unreachable)))
            ;; Shared D: second call returns 1 (only the shared instance was incremented once)
            (if (i32.ne (call $d_inc) (i32.const 1)) (then (unreachable)))
            (call $attest)
        )
        (start $start)
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core func $d_inc_lowered (canon lower (func $d_inc)))
    (core func $b_go_lowered (canon lower (func $b_go)))
    (core func $c_run_lowered (canon lower (func $c_run)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "d-inc" (func $d_inc_lowered))
            (export "b-go" (func $b_go_lowered))
            (export "c-run" (func $c_run_lowered))
        ))
    ))
)
