(component
    (import "attest" (func $attest))
    (import "cov:blob/api" (instance $blob-api
        (export "blob" (type (sub resource)))
        (export "[method]blob.read" (func (param "self" (borrow 0)) (result (list u8))))
        (export "[method]blob.eq" (func (param "self" (borrow 0)) (param "other" (borrow 0)) (result bool)))
    ))
    (alias export $blob-api "blob" (type $blob))
    (import "cov:sign/api" (instance $sign-api
        (export "principal" (type (sub resource)))
        (export "signature" (type (sub resource)))
        (export "signer" (type (sub resource)))
        (export "[method]signer.principal" (func (param "self" (borrow 2)) (result (own 0))))
        (export "[method]principal.eq" (func (param "self" (borrow 0)) (param "other" (borrow 0)) (result bool)))
    ))
    (alias export $sign-api "principal" (type $principal))
    (alias export $sign-api "signature" (type $signature))
    (alias export $sign-api "signer" (type $signer))
    (alias export $sign-api "[method]signer.principal" (func $signer-principal))
    (alias export $sign-api "[method]principal.eq" (func $principal-eq))
    (import "generate-signer" (func $generate-signer (result (own $signer))))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $generate_signer_lowered (canon lower (func $generate-signer)))
    (core func $signer_principal_lowered (canon lower (func $signer-principal)))
    (core func $principal_eq_lowered (canon lower (func $principal-eq)))
    (core func $signer_drop (canon resource.drop $signer))
    (core func $principal_drop (canon resource.drop $principal))

    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "generate-signer" (func $generate_signer (result i32)))
        (import "env" "signer-principal" (func $signer_principal (param i32) (result i32)))
        (import "env" "principal-eq" (func $principal_eq (param i32 i32) (result i32)))
        (import "env" "signer-drop" (func $signer_drop (param i32)))
        (import "env" "principal-drop" (func $principal_drop (param i32)))
        (func $start
            (local $signer_a i32)
            (local $signer_b i32)
            (local $p1 i32)
            (local $p2 i32)
            (local $p3 i32)
            ;; Same signer → two principal calls → should be equal
            (local.set $signer_a (call $generate_signer))
            (local.set $p1 (call $signer_principal (local.get $signer_a)))
            (local.set $p2 (call $signer_principal (local.get $signer_a)))
            ;; p1 == p2 should be true
            (if (i32.eqz (call $principal_eq (local.get $p1) (local.get $p2)))
                (then (unreachable))
            )
            ;; Different signer → principal should differ
            (local.set $signer_b (call $generate_signer))
            (local.set $p3 (call $signer_principal (local.get $signer_b)))
            ;; p1 != p3 should be true
            (if (call $principal_eq (local.get $p1) (local.get $p3))
                (then (unreachable))
            )
            ;; All checks passed
            (call $attest)
            ;; Cleanup
            (call $signer_drop (local.get $signer_a))
            (call $signer_drop (local.get $signer_b))
            (call $principal_drop (local.get $p1))
            (call $principal_drop (local.get $p2))
            (call $principal_drop (local.get $p3))
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "generate-signer" (func $generate_signer_lowered))
            (export "signer-principal" (func $signer_principal_lowered))
            (export "principal-eq" (func $principal_eq_lowered))
            (export "signer-drop" (func $signer_drop))
            (export "principal-drop" (func $principal_drop))
        ))
    ))
)
