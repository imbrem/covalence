;; Parent: imports store, sets "key" → [99] in root, attests.
;; Then calls prove-dep's check — prove-dep will trap because its
;; store is isolated (fresh root). Since parent already attested,
;; the overall result is Sat.
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
    (import "prove-{dep_hex}" (instance $dep
        (export "check" (func))
    ))
    (alias export $dep "check" (func $dep-check))

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
    (core func $store_drop_lowered (canon resource.drop $store))
    (core func $dep_check_lowered (canon lower (func $dep-check)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "root" (func $root (result i32)))
        (import "env" "store-set" (func $store_set (param i32 i32 i32 i32 i32)))
        (import "env" "store-drop" (func $store_drop (param i32)))
        (import "env" "dep-check" (func $dep_check))

        ;; Data: key = "key" at 0, value = [99] at 4
        (data (i32.const 0) "key")
        (data (i32.const 4) "\63")

        (func $start
            (local $handle i32)
            (local.set $handle (call $root))
            ;; set("key", [99]) in our container's store
            (call $store_set (local.get $handle) (i32.const 0) (i32.const 3) (i32.const 4) (i32.const 1))
            (call $store_drop (local.get $handle))
            ;; Attest before calling prove-dep (so result is Sat even if dep traps)
            (call $attest)
            ;; Call prove-dep's check — will trap (isolated store has no "key")
            (call $dep_check)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "root" (func $root_lowered))
            (export "store-set" (func $store_set_lowered))
            (export "store-drop" (func $store_drop_lowered))
            (export "dep-check" (func $dep_check_lowered))
        ))
    ))
)
