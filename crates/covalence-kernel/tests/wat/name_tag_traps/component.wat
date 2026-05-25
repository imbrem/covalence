;; Test: name.tag() currently always traps.
;; Call attest first, then call tag — the trap should not prevent Sat.
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
    (alias export $api "[constructor]name" (func $name-new))
    (alias export $api "[method]name.tag" (func $name-tag))
    (import "blob-{hash_hex}" (func $get-blob (result (own $blob))))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $get_blob_lowered (canon lower (func $get-blob)))
    (core func $name_new_lowered (canon lower (func $name-new)))
    (core func $name_tag_lowered (canon lower (func $name-tag)))
    (core func $blob_drop_lowered (canon resource.drop $blob))
    (core func $name_drop_lowered (canon resource.drop $name))

    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "get-blob" (func $get_blob (result i32)))
        (import "env" "name-new" (func $name_new (param i32) (result i32)))
        (import "env" "name-tag" (func $name_tag (param i32) (result i32)))
        (import "env" "blob-drop" (func $blob_drop (param i32)))
        (import "env" "name-drop" (func $name_drop (param i32)))
        (func $start
            (local $blob i32)
            (local $name i32)
            (local $tag_result i32)
            ;; Get blob, cons to name
            (local.set $blob (call $get_blob))
            (local.set $name (call $name_new (local.get $blob)))
            (call $blob_drop (local.get $blob))
            ;; Attest first so we get Sat even if tag traps
            (call $attest)
            ;; tag() should trap — this is expected
            (local.set $tag_result (call $name_tag (local.get $name)))
            ;; If we somehow get here, drop everything
            (call $name_drop (local.get $name))
            (call $name_drop (local.get $tag_result))
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "get-blob" (func $get_blob_lowered))
            (export "name-new" (func $name_new_lowered))
            (export "name-tag" (func $name_tag_lowered))
            (export "blob-drop" (func $blob_drop_lowered))
            (export "name-drop" (func $name_drop_lowered))
        ))
    ))
)
