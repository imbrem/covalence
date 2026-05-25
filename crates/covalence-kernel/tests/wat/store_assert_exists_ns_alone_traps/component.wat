;; Store assert-exists ns alone traps: open ns("sub") without setting anything at "sub",
;; then assert-exists("sub") — traps because ns alone doesn't mark presence.
;; No attest called before trap, so result should be Unknown.
(component
    (import "attest" (func $attest))
    (import "store" (instance $store-api
        (export "store" (type (sub resource)))
        (export "root" (func (result (own 0))))
        (export "[method]store.assert-exists" (func (param "self" (borrow 0)) (param "key" string)))
        (export "[method]store.ns" (func (param "self" (borrow 0)) (param "key" string) (result (own 0))))
        (export "[method]store.clone" (func (param "self" (borrow 0)) (result (own 0))))
        (export "[method]store.read-only" (func (param "self" (borrow 0)) (result (own 0))))
        (export "new" (func (result (own 0))))
    ))
    (alias export $store-api "store" (type $store))
    (alias export $store-api "root" (func $root))
    (alias export $store-api "[method]store.assert-exists" (func $store-assert-exists))
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
    (core func $store_assert_exists_lowered (canon lower (func $store-assert-exists) (memory $mem) (realloc $realloc_fn)))
    (core func $store_ns_lowered (canon lower (func $store-ns) (memory $mem) (realloc $realloc_fn)))
    (core func $store_drop_lowered (canon resource.drop $store))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-assert-exists" (func $store_assert_exists (param i32 i32 i32)))
        (import "env" "store-ns" (func $store_ns (param i32 i32 i32) (result i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))

        ;; Data: "sub" at 0
        (data (i32.const 0) "sub")

        (func $start
            (local $root_h i32)
            (local $sub_h i32)
            (local.set $root_h (call $root))
            ;; Open ns("sub") — does not mark "sub" as existing
            (local.set $sub_h (call $store_ns (local.get $root_h) (i32.const 0) (i32.const 3)))
            ;; Drop the sub-handle (not needed)
            (call $store_drop (local.get $sub_h))
            ;; assert-exists(root, "sub") — should trap
            (call $store_assert_exists (local.get $root_h) (i32.const 0) (i32.const 3))
            ;; Never reached
            (call $store_drop (local.get $root_h))
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "root" (func $root_lowered))
            (export "store-assert-exists" (func $store_assert_exists_lowered))
            (export "store-ns" (func $store_ns_lowered))
            (export "store-drop" (func $store_drop_lowered))
        ))
    ))
)
