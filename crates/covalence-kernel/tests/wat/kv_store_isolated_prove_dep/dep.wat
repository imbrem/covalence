;; Prove-dep: imports map-shared, calls get("key") — traps (fresh isolated store).
;; Exports a "check" function that triggers the get.
(component
    (import "attest" (func $attest))
    (import "map-shared" (instance $store
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

        (data (i32.const 0) "key")

        ;; check: get("key") — will trap if key not found (isolated store)
        (func $check
            (call $kv_get (i32.const 0) (i32.const 3) (i32.const 64))
            (call $attest)
        )
        (export "check" (func $check))
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "kv-get" (func $kv_get_lowered))
        ))
    ))

    (func $check (canon lift (core func $i "check")))
    (export "check" (func $check))
)
