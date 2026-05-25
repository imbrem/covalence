;; Reader: imports store, exports read-val that returns get("key") first byte.
(component
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

    (core func $root_lowered (canon lower (func $root)))
    (core func $store_get_lowered (canon lower (func $store-get) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-get" (func $store_get (param i32 i32 i32 i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; Data: key = "key" at 0
        (data (i32.const 0) "key")

        ;; read-val: get("key") from root, return first byte as i32
        (func $read_val (result i32)
            (local $handle i32)
            (local.set $handle (call $root))
            ;; get("key") → retptr at 64
            (call $store_get (local.get $handle) (i32.const 0) (i32.const 3) (i32.const 64))
            (call $store_drop (local.get $handle))
            ;; Return first byte of value
            (i32.load8_u (i32.load (i32.const 64)))
        )
        (export "read-val" (func $read_val))
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "root" (func $root_lowered))
            (export "store-get" (func $store_get_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))

    (func $read-val (result s32)
        (canon lift (core func $i "read-val"))
    )
    (export "read-val" (func $read-val))
)
