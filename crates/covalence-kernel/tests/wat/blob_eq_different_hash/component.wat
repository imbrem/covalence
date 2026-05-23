(component
    (import "attest" (func $attest))
    (import "cov:blob/api" (instance $blob-api
        (export "blob" (type (sub resource)))
        (export "[method]blob.read" (func (param "self" (borrow 0)) (result (list u8))))
        (export "[method]blob.eq" (func (param "self" (borrow 0)) (param "other" (borrow 0)) (result bool)))
    ))
    (alias export $blob-api "blob" (type $blob))
    (alias export $blob-api "[method]blob.eq" (func $blob-eq))
    (import "blob-{hex_a}" (func $get-blob-a (result (own $blob))))
    (import "blob-{hex_b}" (func $get-blob-b (result (own $blob))))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $get_blob_a_lowered (canon lower (func $get-blob-a)))
    (core func $get_blob_b_lowered (canon lower (func $get-blob-b)))
    (core func $blob_eq_lowered (canon lower (func $blob-eq)))
    (core func $blob_drop_lowered (canon resource.drop $blob))

    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "get-blob-a" (func $get_blob_a (result i32)))
        (import "env" "get-blob-b" (func $get_blob_b (result i32)))
        (import "env" "blob-eq" (func $blob_eq (param i32 i32) (result i32)))
        (import "env" "blob-drop" (func $blob_drop (param i32)))
        (func $start
            (local $a i32)
            (local $b i32)
            (local.set $a (call $get_blob_a))
            (local.set $b (call $get_blob_b))
            ;; eq should return false (0) for different blobs
            ;; If eq returns false, attest (we expect this path)
            (if (i32.eqz (call $blob_eq (local.get $a) (local.get $b)))
                (then (call $attest))
            )
            (call $blob_drop (local.get $a))
            (call $blob_drop (local.get $b))
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "get-blob-a" (func $get_blob_a_lowered))
            (export "get-blob-b" (func $get_blob_b_lowered))
            (export "blob-eq" (func $blob_eq_lowered))
            (export "blob-drop" (func $blob_drop_lowered))
        ))
    ))
)
