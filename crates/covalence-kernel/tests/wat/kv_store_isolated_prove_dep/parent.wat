;; Parent: imports map-shared, sets "key" → [99], attests.
;; Then calls prove-dep's check — prove-dep will trap because its
;; map-shared is isolated (fresh store). Since parent already attested,
;; the overall result is Sat.
(component
    (import "attest" (func $attest))
    (import "map-shared" (instance $store
        (export "set" (func (param "key" string) (param "value" (list u8))))
        (export "get" (func (param "key" string) (result (list u8))))
    ))
    (alias export $store "set" (func $kv-set))
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
    (core func $kv_set_lowered (canon lower (func $kv-set) (memory $mem) (realloc $realloc_fn)))
    (core func $dep_check_lowered (canon lower (func $dep-check)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "kv-set" (func $kv_set (param i32 i32 i32 i32)))
        (import "env" "dep-check" (func $dep_check))

        ;; Data: key = "key" at 0, value = [99] at 4
        (data (i32.const 0) "key")
        (data (i32.const 4) "\63")

        (func $start
            ;; set("key", [99]) in our container's store
            (call $kv_set (i32.const 0) (i32.const 3) (i32.const 4) (i32.const 1))
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
            (export "kv-set" (func $kv_set_lowered))
            (export "dep-check" (func $dep_check_lowered))
        ))
    ))
)
