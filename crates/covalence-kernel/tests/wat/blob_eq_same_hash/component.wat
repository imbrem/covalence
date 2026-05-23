(component
    (import "attest" (func $attest))
    (import "cov:blob/api" (instance $blob-api
        (export "blob" (type (sub resource)))
        (export "[method]blob.read" (func (param "self" (borrow 0)) (result (list u8))))
        (export "[method]blob.eq" (func (param "self" (borrow 0)) (param "other" (borrow 0)) (result bool)))
    ))
    (alias export $blob-api "blob" (type $blob))
    (alias export $blob-api "[method]blob.eq" (func $blob-eq))
    (import "blob-{hash_hex}" (func $get-blob (result (own $blob))))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $get_blob_lowered (canon lower (func $get-blob)))
    (core func $blob_eq_lowered (canon lower (func $blob-eq)))
    (core func $blob_drop_lowered (canon resource.drop $blob))

    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "get-blob" (func $get_blob (result i32)))
        (import "env" "blob-eq" (func $blob_eq (param i32 i32) (result i32)))
        (import "env" "blob-drop" (func $blob_drop (param i32)))
        (func $start
            (local $a i32)
            (local $b i32)
            ;; Get two handles to the same blob
            (local.set $a (call $get_blob))
            (local.set $b (call $get_blob))
            ;; If eq returns true (1), attest
            (if (call $blob_eq (local.get $a) (local.get $b))
                (then (call $attest))
            )
            ;; Drop both handles
            (call $blob_drop (local.get $a))
            (call $blob_drop (local.get $b))
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "get-blob" (func $get_blob_lowered))
            (export "blob-eq" (func $blob_eq_lowered))
            (export "blob-drop" (func $blob_drop_lowered))
        ))
    ))
)
