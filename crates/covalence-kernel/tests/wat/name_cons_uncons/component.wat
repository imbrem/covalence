;; Test: cons(blob) -> name, then uncons(name) -> blob, then read blob data.
;; If the roundtrip succeeds (read doesn't trap), attest.
(component
    (import "attest" (func $attest))
    (import "cov:blob/api" (instance $api
        ;; Resource types first (blob=0, name=1)
        (export "blob" (type (sub resource)))
        (export "name" (type (sub resource)))
        ;; Blob methods
        (export "[method]blob.read" (func (param "self" (borrow 0)) (result (list u8))))
        (export "[method]blob.eq" (func (param "self" (borrow 0)) (param "other" (borrow 0)) (result bool)))
        ;; Name methods
        (export "[constructor]name" (func (param "b" (borrow 0)) (result (own 1))))
        (export "[method]name.uncons" (func (param "self" (borrow 1)) (result (own 0))))
        (export "[method]name.eq" (func (param "self" (borrow 1)) (param "other" (borrow 1)) (result bool)))
        (export "[static]name.cons" (func (param "tag" (borrow 1)) (param "b" (borrow 0)) (result (own 1))))
        (export "[method]name.repr" (func (param "self" (borrow 1)) (result (own 0))))
        (export "[method]name.tag" (func (param "self" (borrow 1)) (result (own 1))))
    ))
    (alias export $api "blob" (type $blob))
    (alias export $api "name" (type $name))
    (alias export $api "[method]blob.read" (func $blob-read))
    (alias export $api "[constructor]name" (func $name-cons))
    (alias export $api "[method]name.uncons" (func $name-uncons))
    (import "blob-{hash_hex}" (func $get-blob (result (own $blob))))

    ;; Allocator module provides memory and realloc for list lowering
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

    (core func $attest_lowered (canon lower (func $attest)))
    (core func $get_blob_lowered (canon lower (func $get-blob)))
    (core func $name_cons_lowered (canon lower (func $name-cons)))
    (core func $name_uncons_lowered (canon lower (func $name-uncons)))
    (core func $blob_read_lowered (canon lower (func $blob-read) (memory $mem) (realloc $realloc_fn)))
    (core func $blob_drop_lowered (canon resource.drop $blob))
    (core func $name_drop_lowered (canon resource.drop $name))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "get-blob" (func $get_blob (result i32)))
        (import "env" "name-cons" (func $name_cons (param i32) (result i32)))
        (import "env" "name-uncons" (func $name_uncons (param i32) (result i32)))
        (import "env" "blob-read" (func $blob_read (param i32 i32)))
        (import "env" "blob-drop" (func $blob_drop (param i32)))
        (import "env" "name-drop" (func $name_drop (param i32)))
        (func $start
            (local $blob_handle i32)
            (local $name_handle i32)
            (local $blob2_handle i32)
            ;; Get a blob handle from import
            (local.set $blob_handle (call $get_blob))
            ;; cons: blob -> name
            (local.set $name_handle (call $name_cons (local.get $blob_handle)))
            ;; Drop original blob
            (call $blob_drop (local.get $blob_handle))
            ;; uncons: name -> blob
            (local.set $blob2_handle (call $name_uncons (local.get $name_handle)))
            ;; Drop name
            (call $name_drop (local.get $name_handle))
            ;; Read the roundtripped blob (writes ptr+len at retptr offset 0)
            (call $blob_read (local.get $blob2_handle) (i32.const 0))
            ;; Drop the blob
            (call $blob_drop (local.get $blob2_handle))
            ;; If we got here without trapping, the roundtrip succeeded
            (call $attest)
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "get-blob" (func $get_blob_lowered))
            (export "name-cons" (func $name_cons_lowered))
            (export "name-uncons" (func $name_uncons_lowered))
            (export "blob-read" (func $blob_read_lowered))
            (export "blob-drop" (func $blob_drop_lowered))
            (export "name-drop" (func $name_drop_lowered))
        ))
    ))
)
