;; Imports map-a and map-b. Sets "k" → [10] in map-a, sets "k" → [20] in map-b.
;; Gets from both and verifies values are distinct (stores are independent).
(component
    (import "attest" (func $attest))
    (import "map-a" (instance $store_a
        (export "set" (func (param "key" string) (param "value" (list u8))))
        (export "get" (func (param "key" string) (result (list u8))))
    ))
    (import "map-b" (instance $store_b
        (export "set" (func (param "key" string) (param "value" (list u8))))
        (export "get" (func (param "key" string) (result (list u8))))
    ))
    (alias export $store_a "set" (func $a-set))
    (alias export $store_a "get" (func $a-get))
    (alias export $store_b "set" (func $b-set))
    (alias export $store_b "get" (func $b-get))

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
    (core func $a_set_lowered (canon lower (func $a-set) (memory $mem) (realloc $realloc_fn)))
    (core func $a_get_lowered (canon lower (func $a-get) (memory $mem) (realloc $realloc_fn)))
    (core func $b_set_lowered (canon lower (func $b-set) (memory $mem) (realloc $realloc_fn)))
    (core func $b_get_lowered (canon lower (func $b-get) (memory $mem) (realloc $realloc_fn)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "a-set" (func $a_set (param i32 i32 i32 i32)))
        (import "env" "a-get" (func $a_get (param i32 i32 i32)))
        (import "env" "b-set" (func $b_set (param i32 i32 i32 i32)))
        (import "env" "b-get" (func $b_get (param i32 i32 i32)))

        ;; key = "k" at 0, val_a = [10] at 4, val_b = [20] at 8
        (data (i32.const 0) "k")
        (data (i32.const 4) "\0a")
        (data (i32.const 8) "\14")

        (func $start
            ;; map-a: set("k", [10])
            (call $a_set (i32.const 0) (i32.const 1) (i32.const 4) (i32.const 1))
            ;; map-b: set("k", [20])
            (call $b_set (i32.const 0) (i32.const 1) (i32.const 8) (i32.const 1))

            ;; map-a: get("k") → retptr at 64
            (call $a_get (i32.const 0) (i32.const 1) (i32.const 64))
            ;; Check len == 1 and value == 10
            (if (i32.ne (i32.load (i32.const 68)) (i32.const 1))
                (then (unreachable))
            )
            (if (i32.ne (i32.load8_u (i32.load (i32.const 64))) (i32.const 10))
                (then (unreachable))
            )

            ;; map-b: get("k") → retptr at 80
            (call $b_get (i32.const 0) (i32.const 1) (i32.const 80))
            ;; Check len == 1 and value == 20
            (if (i32.ne (i32.load (i32.const 84)) (i32.const 1))
                (then (unreachable))
            )
            (if (i32.ne (i32.load8_u (i32.load (i32.const 80))) (i32.const 20))
                (then (unreachable))
            )

            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "a-set" (func $a_set_lowered))
            (export "a-get" (func $a_get_lowered))
            (export "b-set" (func $b_set_lowered))
            (export "b-get" (func $b_get_lowered))
        ))
    ))
)
