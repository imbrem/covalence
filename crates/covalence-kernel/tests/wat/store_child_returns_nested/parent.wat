;; Parent: links child, calls get-sandbox() to get a nested store handle,
;; reads "data" from it, verifies == [55]. The parent only sees keys within
;; the "sandbox" sub-store — it cannot access root or sibling namespaces.
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
    (alias export $store-api "[method]store.get" (func $store-get))
    (import "link-{child_hex}" (instance $child
        (export "get-sandbox" (func (result (own $store))))
    ))
    (alias export $child "get-sandbox" (func $get-sandbox))

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
    (core func $store_get_lowered (canon lower (func $store-get) (memory $mem) (realloc $realloc_fn)))
    (core func $get_sandbox_lowered (canon lower (func $get-sandbox)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "store-get" (func $store_get (param i32 i32 i32 i32)))
        (import "env" "get-sandbox" (func $get_sandbox (result i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; "data" at 0
        (data (i32.const 0) "data")

        (func $start
            (local $nested i32)
            ;; Get the sandbox handle from the child
            (local.set $nested (call $get_sandbox))

            ;; Read "data" from the nested store → retptr at 64
            (call $store_get (local.get $nested) (i32.const 0) (i32.const 4) (i32.const 64))

            ;; Check len == 1
            (if (i32.ne (i32.load (i32.const 68)) (i32.const 1))
                (then (unreachable))
            )
            ;; Check value == 55
            (if (i32.ne (i32.load8_u (i32.load (i32.const 64))) (i32.const 55))
                (then (unreachable))
            )

            (call $store_drop (local.get $nested))
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "store-get" (func $store_get_lowered))
            (export "get-sandbox" (func $get_sandbox_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))
)
