;; Store try-get existing: set "k" → [5], try-get("k"), verify option discriminant = 1
;; (some) and value = [5]. Attest.
(component
    (import "attest" (func $attest))
    (import "store" (instance $store-api
        (export "store" (type (sub resource)))
        (export "root" (func (result (own 0))))
        (export "[method]store.set" (func (param "self" (borrow 0)) (param "key" string) (param "value" (list u8))))
        (export "[method]store.try-get" (func (param "self" (borrow 0)) (param "key" string) (result (option (list u8)))))
        (export "[method]store.ns" (func (param "self" (borrow 0)) (param "key" string) (result (own 0))))
        (export "[method]store.clone" (func (param "self" (borrow 0)) (result (own 0))))
        (export "[method]store.read-only" (func (param "self" (borrow 0)) (result (own 0))))
        (export "new" (func (result (own 0))))
    ))
    (alias export $store-api "store" (type $store))
    (alias export $store-api "root" (func $root))
    (alias export $store-api "[method]store.set" (func $store-set))
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
    (core func $store_set_lowered (canon lower (func $store-set) (memory $mem) (realloc $realloc_fn)))
    ;; try-get returns (disc: i32, ptr: i32, len: i32) via retptr
    (core func $store_try_get_lowered (canon lower (func $store-try-get) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-set" (func $store_set (param i32 i32 i32 i32 i32)))
        ;; try-get(handle, key_ptr, key_len, retptr)
        (import "env" "store-try-get" (func $store_try_get (param i32 i32 i32 i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; Data: "k" at 0, [5] at 4
        (data (i32.const 0) "k")
        (data (i32.const 4) "\05")

        (func $start
            (local $handle i32)
            ;; Get root
            (local.set $handle (call $root))
            ;; set(handle, "k", [5])
            (call $store_set (local.get $handle) (i32.const 0) (i32.const 1) (i32.const 4) (i32.const 1))
            ;; try-get(handle, "k") → retptr at 64
            ;; retptr layout: [disc: i32, ptr: i32, len: i32]
            (call $store_try_get (local.get $handle) (i32.const 0) (i32.const 1) (i32.const 64))
            ;; Check disc == 1 (some)
            (if (i32.ne (i32.load (i32.const 64)) (i32.const 1))
                (then (unreachable))
            )
            ;; Check len == 1
            (if (i32.ne (i32.load (i32.const 72)) (i32.const 1))
                (then (unreachable))
            )
            ;; Check value == 5
            (if (i32.ne (i32.load8_u (i32.load (i32.const 68))) (i32.const 5))
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
            (export "store-try-get" (func $store_try_get_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))
)
