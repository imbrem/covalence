;; Parent: sets "a" → [1] in its map-data, calls prove-dep (which sets "b" → [2]
;; in its own isolated map-data), then gets "a" back to verify it's still [1].
;; Both parent and child independently set+get from their own stores.
(component
    (import "attest" (func $attest))
    (import "map-data" (instance $store
        (export "set" (func (param "key" string) (param "value" (list u8))))
        (export "get" (func (param "key" string) (result (list u8))))
    ))
    (alias export $store "set" (func $kv-set))
    (alias export $store "get" (func $kv-get))
    (import "prove-{dep_hex}" (instance $dep
        (export "run" (func))
    ))
    (alias export $dep "run" (func $dep-run))

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
    (core func $dep_run_lowered (canon lower (func $dep-run)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "kv-set" (func $kv_set (param i32 i32 i32 i32)))
        (import "env" "kv-get" (func $kv_get (param i32 i32 i32)))
        (import "env" "dep-run" (func $dep_run))

        ;; key = "a" at 0, value = [1] at 4
        (data (i32.const 0) "a")
        (data (i32.const 4) "\01")

        (func $start
            ;; 1. Parent sets "a" → [1]
            (call $kv_set (i32.const 0) (i32.const 1) (i32.const 4) (i32.const 1))

            ;; 2. Call prove-dep — it independently sets "b" → [2] and attests
            (call $dep_run)

            ;; 3. Parent gets "a" back — should still be [1]
            (call $kv_get (i32.const 0) (i32.const 1) (i32.const 64))
            (if (i32.ne (i32.load (i32.const 68)) (i32.const 1))
                (then (unreachable))
            )
            (if (i32.ne (i32.load8_u (i32.load (i32.const 64))) (i32.const 1))
                (then (unreachable))
            )

            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "kv-set" (func $kv_set_lowered))
            (export "kv-get" (func $kv_get_lowered))
            (export "dep-run" (func $dep_run_lowered))
        ))
    ))
)
