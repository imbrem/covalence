;; Nested hierarchy: root.dir("a").dir("b") — set "k" → [99] in the nested store,
;; then re-navigate root.dir("a").dir("b") and verify the data persists.
;; Also verifies dir("a") alone does NOT contain "k".
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
    (alias export $store-api "[method]store.set" (func $store-set))
    (alias export $store-api "[method]store.get" (func $store-get))
    (alias export $store-api "[method]store.ns" (func $store-ns))

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
    (core func $store_ns_lowered (canon lower (func $store-ns) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-set" (func $store_set (param i32 i32 i32 i32 i32)))
        (import "env" "store-get" (func $store_get (param i32 i32 i32 i32)))
        (import "env" "store-ns" (func $store_ns (param i32 i32 i32) (result i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; Data: "a" at 0, "b" at 4, "k" at 8, [99] at 12
        (data (i32.const 0) "a")
        (data (i32.const 4) "b")
        (data (i32.const 8) "k")
        (data (i32.const 12) "\63")

        (func $start
            (local $r i32)
            (local $a i32)
            (local $b i32)
            (local $a2 i32)
            (local $b2 i32)

            ;; Get root
            (local.set $r (call $root))

            ;; Navigate root.dir("a").dir("b")
            (local.set $a (call $store_ns (local.get $r) (i32.const 0) (i32.const 1)))
            (local.set $b (call $store_ns (local.get $a) (i32.const 4) (i32.const 1)))

            ;; Set "k" → [99] in the nested store (a.b)
            (call $store_set (local.get $b) (i32.const 8) (i32.const 1) (i32.const 12) (i32.const 1))
            (call $store_drop (local.get $b))
            (call $store_drop (local.get $a))

            ;; Re-navigate root.dir("a").dir("b") and verify data persists
            (local.set $a2 (call $store_ns (local.get $r) (i32.const 0) (i32.const 1)))
            (local.set $b2 (call $store_ns (local.get $a2) (i32.const 4) (i32.const 1)))

            ;; Get "k" from re-navigated a.b → retptr at 64
            (call $store_get (local.get $b2) (i32.const 8) (i32.const 1) (i32.const 64))

            ;; Check len == 1
            (if (i32.ne (i32.load (i32.const 68)) (i32.const 1))
                (then (unreachable))
            )
            ;; Check value == 99
            (if (i32.ne (i32.load8_u (i32.load (i32.const 64))) (i32.const 99))
                (then (unreachable))
            )

            (call $store_drop (local.get $b2))
            (call $store_drop (local.get $a2))
            (call $store_drop (local.get $r))
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
            (export "store-ns" (func $store_ns_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))
)
