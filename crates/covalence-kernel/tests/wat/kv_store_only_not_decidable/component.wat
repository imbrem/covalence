;; KV store only: imports only map-foo (no attest). Should be Unsat.
(component
    (import "map-foo" (instance $store
        (export "set" (func (param "key" string) (param "value" (list u8))))
        (export "get" (func (param "key" string) (result (list u8))))
    ))
    (alias export $store "set" (func $kv-set))

    (core module $alloc_mod
        (memory 1)
        (export "memory" (memory 0))
        (func $realloc (param i32 i32 i32 i32) (result i32)
            (i32.const 0x1000)
        )
        (export "cabi_realloc" (func $realloc))
    )
    (core instance $alloc (instantiate $alloc_mod))
    (alias core export $alloc "memory" (core memory $mem))
    (alias core export $alloc "cabi_realloc" (core func $realloc_fn))

    (core func $kv_set_lowered (canon lower (func $kv-set) (memory $mem) (realloc $realloc_fn)))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "kv-set" (func $kv_set (param i32 i32 i32 i32)))

        (data (i32.const 0) "key")
        (data (i32.const 4) "\ff")

        (func $start
            (call $kv_set (i32.const 0) (i32.const 3) (i32.const 4) (i32.const 1))
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "kv-set" (func $kv_set_lowered))
        ))
    ))
)
