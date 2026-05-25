;; Prove-dep: imports store, calls get("key") from root — traps (fresh isolated store).
;; Exports a "check" function that triggers the get.
(component
    (import "attest" (func $attest))
    (import "store" (instance $store-api
        (export "store" (type (sub resource)))
        (export "root" (func (result (own 0))))
        (export "[method]store.set" (func (param "self" (borrow 0)) (param "key" string) (param "value" (list u8))))
        (export "[method]store.get" (func (param "self" (borrow 0)) (param "key" string) (result (list u8))))
        (export "[method]store.ns" (func (param "self" (borrow 0)) (param "key" string) (result (own 0))))
        (export "[method]store.clone" (func (param "self" (borrow 0)) (result (own 0))))
        (export "[method]store.read-only" (func (param "self" (borrow 0)) (result (own 0))))
        (export "new" (func (result (own 0))))
    ))
    (alias export $store-api "store" (type $store))
    (alias export $store-api "root" (func $root))
    (alias export $store-api "[method]store.get" (func $store-get))

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
    (core func $store_get_lowered (canon lower (func $store-get) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-get" (func $store_get (param i32 i32 i32 i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        (data (i32.const 0) "key")

        ;; check: get("key") from root — will trap if key not found (isolated store)
        (func $check
            (local $handle i32)
            (local.set $handle (call $root))
            (call $store_get (local.get $handle) (i32.const 0) (i32.const 3) (i32.const 64))
            (call $store_drop (local.get $handle))
            (call $attest)
        )
        (export "check" (func $check))
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "root" (func $root_lowered))
            (export "store-get" (func $store_get_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))

    (func $check (canon lift (core func $i "check")))
    (export "check" (func $check))
)
