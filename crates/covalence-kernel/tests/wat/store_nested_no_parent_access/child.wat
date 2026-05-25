;; Child: exports get-restricted() → own<store> pointing at root.dir("restricted").
;; The parent sets "secret" in the root directly. The returned nested handle
;; should NOT be able to see "secret" (it's a different namespace).
(component
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
    (alias export $store-api "[method]store.dir" (func $store-dir))

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
    (core func $store_dir_lowered (canon lower (func $store-dir) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-dir" (func $store_dir (param i32 i32 i32) (result i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; "restricted" at 0
        (data (i32.const 0) "restricted")

        ;; get-restricted: returns handle to root.dir("restricted")
        (func $get_restricted (result i32)
            (local $r i32)
            (local $sub i32)
            (local.set $r (call $root))
            (local.set $sub (call $store_dir (local.get $r) (i32.const 0) (i32.const 10)))
            (call $store_drop (local.get $r))
            (local.get $sub)
        )
        (export "get-restricted" (func $get_restricted))
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "root" (func $root_lowered))
            (export "store-dir" (func $store_dir_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))

    (func $get-restricted (result (own $store))
        (canon lift (core func $i "get-restricted"))
    )
    (export "get-restricted" (func $get-restricted))
)
