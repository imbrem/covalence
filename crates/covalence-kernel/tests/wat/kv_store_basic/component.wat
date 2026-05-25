;; KV store basic: set "hello" → [1,2,3], get "hello" back, attest if match.
(component
    (import "attest" (func $attest))
    (import "map-my-store" (instance $store
        (export "set" (func (param "key" string) (param "value" (list u8))))
        (export "get" (func (param "key" string) (result (list u8))))
    ))
    (alias export $store "set" (func $kv-set))
    (alias export $store "get" (func $kv-get))

    ;; Allocator module provides memory and realloc for string/list ABI
    (core module $alloc_mod
        (memory 1)
        (export "memory" (memory 0))
        (func $realloc (param i32 i32 i32 i32) (result i32)
            ;; Bump allocator: return next free address from global
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

    ;; Lower component functions to core ABI
    (core func $attest_lowered (canon lower (func $attest)))
    ;; set(key_ptr, key_len, val_ptr, val_len)
    (core func $kv_set_lowered (canon lower (func $kv-set) (memory $mem) (realloc $realloc_fn)))
    ;; get(key_ptr, key_len, retptr) — writes (ptr, len) at retptr
    (core func $kv_get_lowered (canon lower (func $kv-get) (memory $mem) (realloc $realloc_fn)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "kv-set" (func $kv_set (param i32 i32 i32 i32)))
        (import "env" "kv-get" (func $kv_get (param i32 i32 i32)))

        ;; Data: key = "hello" at offset 0, value = [1,2,3] at offset 8
        (data (i32.const 0) "hello")
        (data (i32.const 8) "\01\02\03")

        (func $start
            ;; set("hello", [1,2,3])
            ;; key_ptr=0, key_len=5, val_ptr=8, val_len=3
            (call $kv_set (i32.const 0) (i32.const 5) (i32.const 8) (i32.const 3))

            ;; get("hello") → retptr at 64
            ;; key_ptr=0, key_len=5, retptr=64
            (call $kv_get (i32.const 0) (i32.const 5) (i32.const 64))

            ;; retptr has (ptr: i32, len: i32)
            ;; Check len == 3
            (if (i32.ne (i32.load (i32.const 68)) (i32.const 3))
                (then (unreachable))
            )

            ;; Check bytes: [1, 2, 3]
            (if (i32.ne (i32.load8_u (i32.load (i32.const 64))) (i32.const 1))
                (then (unreachable))
            )
            (if (i32.ne (i32.load8_u (i32.add (i32.load (i32.const 64)) (i32.const 1))) (i32.const 2))
                (then (unreachable))
            )
            (if (i32.ne (i32.load8_u (i32.add (i32.load (i32.const 64)) (i32.const 2))) (i32.const 3))
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
        ))
    ))
)
