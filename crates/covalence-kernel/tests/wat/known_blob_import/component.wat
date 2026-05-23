(component
    (import "attest" (func $attest))
    (import "cov:blob/api" (instance $blob-api
        (export "blob" (type (sub resource)))
        (export "[method]blob.read" (func (param "self" (borrow 0)) (result (list u8))))
        (export "[method]blob.eq" (func (param "self" (borrow 0)) (param "other" (borrow 0)) (result bool)))
    ))
    (alias export $blob-api "blob" (type $blob))
    (import "blob-{hash_hex}" (func $get-blob (result (own $blob))))
    (core module $m
        (import "env" "attest" (func $attest))
        (func $start (call $attest))
        (start $start)
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
        ))
    ))
)
