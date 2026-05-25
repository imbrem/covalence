;; KV store get missing: calls get("missing") without setting — should trap.
(component
    (import "attest" (func $attest))
    (import "map-my-store" (instance $store
        (export "set" (func (param "key" string) (param "value" (list u8))))
        (export "get" (func (param "key" string) (result (list u8))))
    ))
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
    (core func $kv_get_lowered (canon lower (func $kv-get) (memory $mem) (realloc $realloc_fn)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "kv-get" (func $kv_get (param i32 i32 i32)))

        (data (i32.const 0) "missing")

        (func $start
            ;; get("missing") — should trap (no value set)
            (call $kv_get (i32.const 0) (i32.const 7) (i32.const 64))
            ;; If we reach here, attest (but we shouldn't)
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "kv-get" (func $kv_get_lowered))
        ))
    ))
)
