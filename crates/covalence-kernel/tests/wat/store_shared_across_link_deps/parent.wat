;; Parent: links writer (first, so it runs start), then reader.
;; Calls reader.read-val, checks result == 42, attests.
(component
    (import "attest" (func $attest))
    (import "link-{writer_hex}" (instance $writer))
    (import "link-{reader_hex}" (instance $reader
        (export "read-val" (func (result s32)))
    ))
    (alias export $reader "read-val" (func $read-val))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $read_val_lowered (canon lower (func $read-val)))

    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "read-val" (func $read_val (result i32)))

        (func $start
            ;; read-val should return 42 (set by writer in shared store)
            (if (i32.ne (call $read_val) (i32.const 42))
                (then (unreachable))
            )
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "read-val" (func $read_val_lowered))
        ))
    ))
)
