;; Store basic: get root, set "hello" → [1,2,3], get "hello" back, attest if match.
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

    ;; Allocator module provides memory and realloc for string/list ABI
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

    ;; Lower component functions to core ABI
    (core func $attest_lowered (canon lower (func $attest)))
    ;; root() -> i32 (handle)
    (core func $root_lowered (canon lower (func $root)))
    ;; set(i32_handle, i32_key_ptr, i32_key_len, i32_val_ptr, i32_val_len)
    (core func $store_set_lowered (canon lower (func $store-set) (memory $mem) (realloc $realloc_fn)))
    ;; get(i32_handle, i32_key_ptr, i32_key_len, i32_retptr)
    (core func $store_get_lowered (canon lower (func $store-get) (memory $mem) (realloc $realloc_fn)))
    ;; drop(i32_handle)
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-set" (func $store_set (param i32 i32 i32 i32 i32)))
        (import "env" "store-get" (func $store_get (param i32 i32 i32 i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; Data: key = "hello" at offset 0, value = [1,2,3] at offset 8
        (data (i32.const 0) "hello")
        (data (i32.const 8) "\01\02\03")

        (func $start
            (local $handle i32)
            ;; Get root store handle
            (local.set $handle (call $root))

            ;; set(handle, "hello", [1,2,3])
            ;; key_ptr=0, key_len=5, val_ptr=8, val_len=3
            (call $store_set (local.get $handle) (i32.const 0) (i32.const 5) (i32.const 8) (i32.const 3))

            ;; get(handle, "hello") → retptr at 64
            (call $store_get (local.get $handle) (i32.const 0) (i32.const 5) (i32.const 64))

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

            ;; Drop store handle
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
        ))
    ))
)
