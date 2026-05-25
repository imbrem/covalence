;; Test: static name.cons(tag, blob) -> name produces a different name
;; than the plain constructor name(blob).
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
    (alias export $api "[static]name.cons" (func $name-cons-tagged))
    (alias export $api "[method]name.eq" (func $name-eq))
    (import "blob-{hex_a}" (func $get-blob-a (result (own $blob))))
    (import "blob-{hex_b}" (func $get-blob-b (result (own $blob))))

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $get_blob_a_lowered (canon lower (func $get-blob-a)))
    (core func $get_blob_b_lowered (canon lower (func $get-blob-b)))
    (core func $name_new_lowered (canon lower (func $name-new)))
    (core func $name_cons_tagged_lowered (canon lower (func $name-cons-tagged)))
    (core func $name_eq_lowered (canon lower (func $name-eq)))
    (core func $blob_drop_lowered (canon resource.drop $blob))
    (core func $name_drop_lowered (canon resource.drop $name))

    (core module $m
        (import "env" "attest" (func $attest))
        (import "env" "get-blob-a" (func $get_blob_a (result i32)))
        (import "env" "get-blob-b" (func $get_blob_b (result i32)))
        (import "env" "name-new" (func $name_new (param i32) (result i32)))
        (import "env" "name-cons-tagged" (func $name_cons_tagged (param i32 i32) (result i32)))
        (import "env" "name-eq" (func $name_eq (param i32 i32) (result i32)))
        (import "env" "blob-drop" (func $blob_drop (param i32)))
        (import "env" "name-drop" (func $name_drop (param i32)))
        (func $start
            (local $ba i32) (local $bb i32)
            (local $tag i32) (local $plain i32) (local $tagged i32)
            ;; Get two blobs
            (local.set $ba (call $get_blob_a))
            (local.set $bb (call $get_blob_b))
            ;; Plain name from blob b
            (local.set $plain (call $name_new (local.get $bb)))
            ;; Tag name from blob a
            (local.set $tag (call $name_new (local.get $ba)))
            ;; Tagged: cons(tag, blob_b) — keyed hash
            (local.set $tagged (call $name_cons_tagged (local.get $tag) (local.get $bb)))
            ;; Drop blobs
            (call $blob_drop (local.get $ba))
            (call $blob_drop (local.get $bb))
            ;; Tagged name should differ from plain name of the same blob
            (if (call $name_eq (local.get $plain) (local.get $tagged))
                (then (unreachable))
            )
            ;; Cleanup
            (call $name_drop (local.get $tag))
            (call $name_drop (local.get $plain))
            (call $name_drop (local.get $tagged))
            ;; All checks passed
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "get-blob-a" (func $get_blob_a_lowered))
            (export "get-blob-b" (func $get_blob_b_lowered))
            (export "name-new" (func $name_new_lowered))
            (export "name-cons-tagged" (func $name_cons_tagged_lowered))
            (export "name-eq" (func $name_eq_lowered))
            (export "blob-drop" (func $blob_drop_lowered))
            (export "name-drop" (func $name_drop_lowered))
        ))
    ))
)
