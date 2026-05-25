;; Test: cons two blobs to names, compare with eq.
;; Same blob -> eq returns true. Different blobs -> eq returns false.
;; Attest iff both checks pass.
(component
    (import "attest" (func $attest))
    (import "cov:blob/api" (instance $api
        (export "blob" (type (sub resource)))
        (export "name" (type (sub resource)))
        (export "[method]blob.read" (func (param "self" (borrow 0)) (result (list u8))))
        (export "[method]blob.eq" (func (param "self" (borrow 0)) (param "other" (borrow 0)) (result bool)))
        (export "[constructor]name" (func (param "b" (borrow 0)) (result (own 1))))
        (export "[method]name.uncons" (func (param "self" (borrow 1)) (result (own 0))))
        (export "[method]name.eq" (func (param "self" (borrow 1)) (param "other" (borrow 1)) (result bool)))
        (export "[static]name.cons" (func (param "tag" (borrow 1)) (param "b" (borrow 0)) (result (own 1))))
        (export "[method]name.repr" (func (param "self" (borrow 1)) (result (own 0))))
        (export "[method]name.tag" (func (param "self" (borrow 1)) (result (own 1))))
    ))
    (alias export $api "blob" (type $blob))
    (alias export $api "name" (type $name))
    (alias export $api "[constructor]name" (func $name-cons))
    (alias export $api "[method]name.eq" (func $name-eq))
    (import "blob-{hex_a}" (func $get-blob-a (result (own $blob))))
    (import "blob-{hex_b}" (func $get-blob-b (result (own $blob))))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $get_blob_a_lowered (canon lower (func $get-blob-a)))
    (core func $get_blob_b_lowered (canon lower (func $get-blob-b)))
    (core func $name_cons_lowered (canon lower (func $name-cons)))
    (core func $name_eq_lowered (canon lower (func $name-eq)))
    (core func $blob_drop_lowered (canon resource.drop $blob))
    (core func $name_drop_lowered (canon resource.drop $name))

    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "get-blob-a" (func $get_blob_a (result i32)))
        (import "env" "get-blob-b" (func $get_blob_b (result i32)))
        (import "env" "name-cons" (func $name_cons (param i32) (result i32)))
        (import "env" "name-eq" (func $name_eq (param i32 i32) (result i32)))
        (import "env" "blob-drop" (func $blob_drop (param i32)))
        (import "env" "name-drop" (func $name_drop (param i32)))
        (func $start
            (local $ba i32) (local $bb i32)
            (local $na1 i32) (local $na2 i32) (local $nb i32)
            ;; Get two blobs
            (local.set $ba (call $get_blob_a))
            (local.set $bb (call $get_blob_b))
            ;; cons each to a name
            (local.set $na1 (call $name_cons (local.get $ba)))
            (local.set $na2 (call $name_cons (local.get $ba)))
            (local.set $nb (call $name_cons (local.get $bb)))
            ;; Drop blobs
            (call $blob_drop (local.get $ba))
            (call $blob_drop (local.get $bb))
            ;; Same blob => names should be equal
            (if (i32.eqz (call $name_eq (local.get $na1) (local.get $na2)))
                (then (unreachable))
            )
            ;; Different blobs => names should not be equal
            (if (call $name_eq (local.get $na1) (local.get $nb))
                (then (unreachable))
            )
            ;; Cleanup
            (call $name_drop (local.get $na1))
            (call $name_drop (local.get $na2))
            (call $name_drop (local.get $nb))
            ;; Both checks passed
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "get-blob-a" (func $get_blob_a_lowered))
            (export "get-blob-b" (func $get_blob_b_lowered))
            (export "name-cons" (func $name_cons_lowered))
            (export "name-eq" (func $name_eq_lowered))
            (export "blob-drop" (func $blob_drop_lowered))
            (export "name-drop" (func $name_drop_lowered))
        ))
    ))
)
