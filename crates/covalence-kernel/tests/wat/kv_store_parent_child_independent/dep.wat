;; Prove-dep: imports its own map-data, sets "b" → [2], gets "b" back,
;; attests if correct. Does NOT see parent's "a" key (isolated store).
(component
    (import "attest" (func $attest))
    (import "map-data" (instance $store
        (export "set" (func (param "key" string) (param "value" (list u8))))
        (export "get" (func (param "key" string) (result (list u8))))
    ))
    (alias export $store "set" (func $kv-set))
    (alias export $store "get" (func $kv-get))

    (core module $alloc_mod
        (memory 1)
        (export "memory" (memory 0))
        (func $realloc (param i32 i32 i32 i32) (result i32)
            (local $ret i32)
            (local.set $ret (global.get $next))
            (global.set $next (i32.add (local.get $ret) (local.get 3)))
            (local.get $ret)
        )
        (global $next (mut i32) (i32.const 0x1000))
        (export "cabi_realloc" (func $realloc))
    )
    (core instance $alloc (instantiate $alloc_mod))
    (alias core export $alloc "memory" (core memory $mem))
    (alias core export $alloc "cabi_realloc" (core func $realloc_fn))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $kv_set_lowered (canon lower (func $kv-set) (memory $mem) (realloc $realloc_fn)))
    (core func $kv_get_lowered (canon lower (func $kv-get) (memory $mem) (realloc $realloc_fn)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "kv-set" (func $kv_set (param i32 i32 i32 i32)))
        (import "env" "kv-get" (func $kv_get (param i32 i32 i32)))

        ;; key = "b" at 0, value = [2] at 4
        (data (i32.const 0) "b")
        (data (i32.const 4) "\02")

        (func $run
            ;; set("b", [2])
            (call $kv_set (i32.const 0) (i32.const 1) (i32.const 4) (i32.const 1))
            ;; get("b") → retptr at 64
            (call $kv_get (i32.const 0) (i32.const 1) (i32.const 64))
            ;; Check len == 1 and value == 2
            (if (i32.ne (i32.load (i32.const 68)) (i32.const 1))
                (then (unreachable))
            )
            (if (i32.ne (i32.load8_u (i32.load (i32.const 64))) (i32.const 2))
                (then (unreachable))
            )
            (call $attest)
        )
        (export "run" (func $run))
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "kv-set" (func $kv_set_lowered))
            (export "kv-get" (func $kv_get_lowered))
        ))
    ))

    (func $run (canon lift (core func $i "run")))
    (export "run" (func $run))
)
