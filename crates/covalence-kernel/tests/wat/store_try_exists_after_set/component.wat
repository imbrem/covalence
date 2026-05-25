;; Store try-exists after set: set "k" → [1], try-exists("k"), verify returns true. Attest.
(component
    (import "attest" (func $attest))
    (import "store" (instance $store-api
        (export "store" (type (sub resource)))
        (export "root" (func (result (own 0))))
        (export "[method]store.set" (func (param "self" (borrow 0)) (param "key" string) (param "value" (list u8))))
        (export "[method]store.try-exists" (func (param "self" (borrow 0)) (param "key" string) (result bool)))
        (export "[method]store.ns" (func (param "self" (borrow 0)) (param "key" string) (result (own 0))))
        (export "[method]store.clone" (func (param "self" (borrow 0)) (result (own 0))))
        (export "[method]store.read-only" (func (param "self" (borrow 0)) (result (own 0))))
        (export "new" (func (result (own 0))))
    ))
    (alias export $store-api "store" (type $store))
    (alias export $store-api "root" (func $root))
    (alias export $store-api "[method]store.set" (func $store-set))
    (alias export $store-api "[method]store.try-exists" (func $store-try-exists))

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
    ;; try-exists returns i32: 0=false, 1=true
    (core func $store_try_exists_lowered (canon lower (func $store-try-exists) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-set" (func $store_set (param i32 i32 i32 i32 i32)))
        ;; try-exists(handle, key_ptr, key_len) -> i32 (0=false, 1=true)
        (import "env" "store-try-exists" (func $store_try_exists (param i32 i32 i32) (result i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; Data: "k" at 0, [1] at 4
        (data (i32.const 0) "k")
        (data (i32.const 4) "\01")

        (func $start
            (local $handle i32)
            (local.set $handle (call $root))
            ;; set(handle, "k", [1])
            (call $store_set (local.get $handle) (i32.const 0) (i32.const 1) (i32.const 4) (i32.const 1))
            ;; try-exists(handle, "k") → should return 1 (true)
            (if (i32.ne (call $store_try_exists (local.get $handle) (i32.const 0) (i32.const 1)) (i32.const 1))
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
            (export "store-try-exists" (func $store_try_exists_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))
)
