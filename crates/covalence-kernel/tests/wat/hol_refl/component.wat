;; HOL REFL proof via WASM component model
;;
;; Proves: |- x = x  (where x : bool)
;;
;; Steps:
;;   1. bool_ty = bool-type()
;;   2. x = mk-var("x", bool_ty)
;;   3. thm = refl(x)
;;   4. attest()

(component
    (import "attest" (func $attest))
    (import "cov:hol/kernel" (instance $hol-api
        (export "hol-type" (type (sub resource)))
        (export "term" (type (sub resource)))
        (export "thm" (type (sub resource)))
        (export "bool-type" (func (result (own 0))))
        (export "mk-var" (func (param "name" string) (param "ty" (borrow 0)) (result (own 1))))
        (export "refl" (func (param "tm" (borrow 1)) (result (own 2))))
    ))
    (alias export $hol-api "hol-type" (type $hol-type))
    (alias export $hol-api "term" (type $term))
    (alias export $hol-api "thm" (type $thm))
    (alias export $hol-api "bool-type" (func $bool-type))
    (alias export $hol-api "mk-var" (func $mk-var))
    (alias export $hol-api "refl" (func $refl))

    ;; Allocator module for string ABI (mk-var takes a string param)
    (core module $alloc_mod
        (memory 1)
        (export "memory" (memory 0))
        (func $realloc (param i32 i32 i32 i32) (result i32)
            (local $ret i32)
            (local.set $ret (global.get $next))
            (global.set $next (i32.add (local.get $ret) (local.get 3)))
            (local.get $ret)
        )
        (global $next (mut i32) (i32.const 0x1000))
        (export "cabi_realloc" (func $realloc))
    )
    (core instance $alloc (instantiate $alloc_mod))
    (alias core export $alloc "memory" (core memory $mem))
    (alias core export $alloc "cabi_realloc" (core func $realloc_fn))

    ;; Lower component functions to core ABI
    (core func $attest_lowered (canon lower (func $attest)))
    ;; bool-type() -> i32 (handle)
    (core func $bool_type_lowered (canon lower (func $bool-type)))
    ;; mk-var(str_ptr, str_len, type_handle) -> i32 (handle)
    (core func $mk_var_lowered (canon lower (func $mk-var) (memory $mem) (realloc $realloc_fn)))
    ;; refl(term_handle) -> i32 (handle)
    (core func $refl_lowered (canon lower (func $refl)))
    ;; Resource drop functions
    (core func $hol_type_drop (canon resource.drop $hol-type))
    (core func $term_drop (canon resource.drop $term))
    (core func $thm_drop (canon resource.drop $thm))

    (core module $m
        (import "alloc" "memory" (memory 1))
        (import "env" "attest" (func $attest))
        (import "env" "bool-type" (func $bool_type (result i32)))
        (import "env" "mk-var" (func $mk_var (param i32 i32 i32) (result i32)))
        (import "env" "refl" (func $refl (param i32) (result i32)))
        (import "env" "hol-type-drop" (func $hol_type_drop (param i32)))
        (import "env" "term-drop" (func $term_drop (param i32)))
        (import "env" "thm-drop" (func $thm_drop (param i32)))

        ;; String "x" at offset 0
        (data (i32.const 0) "x")

        (func $start
            (local $bool_ty i32)
            (local $x i32)
            (local $thm i32)

            ;; 1. bool_ty = bool-type()
            (local.set $bool_ty (call $bool_type))

            ;; 2. x = mk-var("x", bool_ty)
            ;;    string ptr=0, len=1, type handle
            (local.set $x (call $mk_var (i32.const 0) (i32.const 1) (local.get $bool_ty)))

            ;; 3. thm = refl(x) — proves |- x = x
            (local.set $thm (call $refl (local.get $x)))

            ;; 4. Success! Attest.
            (call $attest)

            ;; Cleanup
            (call $thm_drop (local.get $thm))
            (call $term_drop (local.get $x))
            (call $hol_type_drop (local.get $bool_ty))
        )
        (start $start)
    )
    (core instance $i (instantiate $m
        (with "alloc" (instance $alloc))
        (with "env" (instance
            (export "attest" (func $attest_lowered))
            (export "bool-type" (func $bool_type_lowered))
            (export "mk-var" (func $mk_var_lowered))
            (export "refl" (func $refl_lowered))
            (export "hol-type-drop" (func $hol_type_drop))
            (export "term-drop" (func $term_drop))
            (export "thm-drop" (func $thm_drop))
        ))
    ))
)
