;; Parent: sets "a" → [1] in its store root, calls prove-dep (which sets "b" → [2]
;; in its own isolated store root), then gets "a" back to verify it's still [1].
;; Both parent and child independently set+get from their own stores.
(component
    (import "attest" (func $attest))
    (import "store" (instance $store-api
        (export "store" (type (sub resource)))
        (export "root" (func (result (own 0))))
        (export "[method]store.set" (func (param "self" (borrow 0)) (param "key" string) (param "value" (list u8))))
        (export "[method]store.get" (func (param "self" (borrow 0)) (param "key" string) (result (list u8))))
        (export "[method]store.dir" (func (param "self" (borrow 0)) (param "key" string) (result (own 0))))
        (export "[method]store.clone" (func (param "self" (borrow 0)) (result (own 0))))
        (export "[method]store.read-only" (func (param "self" (borrow 0)) (result (own 0))))
        (export "new" (func (result (own 0))))
    ))
    (alias export $store-api "store" (type $store))
    (alias export $store-api "root" (func $root))
    (alias export $store-api "[method]store.set" (func $store-set))
    (alias export $store-api "[method]store.get" (func $store-get))
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
    (core func $root_lowered (canon lower (func $root)))
    (core func $store_set_lowered (canon lower (func $store-set) (memory $mem) (realloc $realloc_fn)))
    (core func $store_get_lowered (canon lower (func $store-get) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))
    (core func $dep_run_lowered (canon lower (func $dep-run)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-set" (func $store_set (param i32 i32 i32 i32 i32)))
        (import "env" "store-get" (func $store_get (param i32 i32 i32 i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))
        (import "env" "dep-run" (func $dep_run))

        ;; key = "a" at 0, value = [1] at 4
        (data (i32.const 0) "a")
        (data (i32.const 4) "\01")

        (func $start
            (local $handle i32)
            ;; 1. Parent sets "a" → [1]
            (local.set $handle (call $root))
            (call $store_set (local.get $handle) (i32.const 0) (i32.const 1) (i32.const 4) (i32.const 1))

            ;; 2. Call prove-dep — it independently sets "b" → [2] and attests
            (call $dep_run)

            ;; 3. Parent gets "a" back — should still be [1]
            (call $store_get (local.get $handle) (i32.const 0) (i32.const 1) (i32.const 64))
            (if (i32.ne (i32.load (i32.const 68)) (i32.const 1))
                (then (unreachable))
            )
            (if (i32.ne (i32.load8_u (i32.load (i32.const 64))) (i32.const 1))
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
            (export "store-set" (func $store_set_lowered))
            (export "store-get" (func $store_get_lowered))
            (export "store-drop" (func $store_drop_lowered))
            (export "dep-run" (func $dep_run_lowered))
        ))
    ))
)
