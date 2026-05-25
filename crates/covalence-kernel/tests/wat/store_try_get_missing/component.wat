;; Store try-get missing: try-get("missing") on empty store, verify disc = 0 (none). Attest.
(component
    (import "attest" (func $attest))
    (import "store" (instance $store-api
        (export "store" (type (sub resource)))
        (export "root" (func (result (own 0))))
        (export "[method]store.try-get" (func (param "self" (borrow 0)) (param "key" string) (result (option (list u8)))))
        (export "[method]store.ns" (func (param "self" (borrow 0)) (param "key" string) (result (own 0))))
        (export "[method]store.clone" (func (param "self" (borrow 0)) (result (own 0))))
        (export "[method]store.read-only" (func (param "self" (borrow 0)) (result (own 0))))
        (export "new" (func (result (own 0))))
    ))
    (alias export $store-api "store" (type $store))
    (alias export $store-api "root" (func $root))
    (alias export $store-api "[method]store.try-get" (func $store-try-get))

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
    (core func $root_lowered (canon lower (func $root)))
    (core func $store_try_get_lowered (canon lower (func $store-try-get) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-try-get" (func $store_try_get (param i32 i32 i32 i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; Data: "missing" at 0
        (data (i32.const 0) "missing")

        (func $start
            (local $handle i32)
            (local.set $handle (call $root))
            ;; try-get(handle, "missing") → retptr at 64
            (call $store_try_get (local.get $handle) (i32.const 0) (i32.const 7) (i32.const 64))
            ;; Check disc == 0 (none)
            (if (i32.ne (i32.load (i32.const 64)) (i32.const 0))
                (then (unreachable))
            )
            (call $store_drop (local.get $handle))
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "root" (func $root_lowered))
            (export "store-try-get" (func $store_try_get_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))
)
