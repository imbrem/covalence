;; Child: imports store, opens root.dir("sandbox"), sets "data" → [55] in it,
;; exports get-sandbox() → own<store> that returns the nested sub-store handle.
;; The parent can only see keys within "sandbox", not the root.
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
    (alias export $store-api "[method]store.set" (func $store-set))
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

    (core func $root_lowered (canon lower (func $root)))
    (core func $store_set_lowered (canon lower (func $store-set) (memory $mem) (realloc $realloc_fn)))
    (core func $store_ns_lowered (canon lower (func $store-ns) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-set" (func $store_set (param i32 i32 i32 i32 i32)))
        (import "env" "store-ns" (func $store_ns (param i32 i32 i32) (result i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; "sandbox" at 0, "data" at 8, [55] at 16
        (data (i32.const 0) "sandbox")
        (data (i32.const 8) "data")
        (data (i32.const 16) "\37")

        ;; Start: populate the sandbox sub-store
        (func $start
            (local $r i32)
            (local $sub i32)
            (local.set $r (call $root))
            (local.set $sub (call $store_ns (local.get $r) (i32.const 0) (i32.const 7)))
            ;; Set "data" → [55] in sandbox
            (call $store_set (local.get $sub) (i32.const 8) (i32.const 4) (i32.const 16) (i32.const 1))
            (call $store_drop (local.get $sub))
            (call $store_drop (local.get $r))
        )
        (start $start)

        ;; get-sandbox: returns a handle to root.dir("sandbox")
        (func $get_sandbox (result i32)
            (local $r i32)
            (local $sub i32)
            (local.set $r (call $root))
            (local.set $sub (call $store_ns (local.get $r) (i32.const 0) (i32.const 7)))
            (call $store_drop (local.get $r))
            (local.get $sub)
        )
        (export "get-sandbox" (func $get_sandbox))
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "root" (func $root_lowered))
            (export "store-set" (func $store_set_lowered))
            (export "store-ns" (func $store_ns_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))

    ;; Lift get-sandbox to component level: returns own<store>
    (func $get-sandbox (result (own $store))
        (canon lift (core func $i "get-sandbox"))
    )
    (export "get-sandbox" (func $get-sandbox))
)
