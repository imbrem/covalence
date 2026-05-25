;; Parent: sets "secret" → [11] in root, then gets a nested handle from the child
;; (pointing at root.dir("restricted")). Tries to get "secret" from the nested
;; handle — traps because "secret" lives in root, not root.dir("restricted").
;; Parent attests BEFORE the trap, so overall result is Sat.
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
    (import "link-{child_hex}" (instance $child
        (export "get-restricted" (func (result (own $store))))
    ))
    (alias export $child "get-restricted" (func $get-restricted))

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
    (core func $get_restricted_lowered (canon lower (func $get-restricted)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-set" (func $store_set (param i32 i32 i32 i32 i32)))
        (import "env" "store-get" (func $store_get (param i32 i32 i32 i32)))
        (import "env" "get-restricted" (func $get_restricted (result i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; "secret" at 0, [11] at 8
        (data (i32.const 0) "secret")
        (data (i32.const 8) "\0b")

        (func $start
            (local $r i32)
            (local $nested i32)

            ;; Set "secret" → [11] in root
            (local.set $r (call $root))
            (call $store_set (local.get $r) (i32.const 0) (i32.const 6) (i32.const 8) (i32.const 1))
            (call $store_drop (local.get $r))

            ;; Attest BEFORE the trap
            (call $attest)

            ;; Get nested handle from child (points to root.dir("restricted"))
            (local.set $nested (call $get_restricted))

            ;; Try to get "secret" from the nested handle — traps!
            ;; "secret" is in root, not in root.dir("restricted")
            (call $store_get (local.get $nested) (i32.const 0) (i32.const 6) (i32.const 64))

            ;; Should NOT reach here
            (unreachable)
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
            (export "get-restricted" (func $get_restricted_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))
)
