(component
    (import "prove-{theory_hex}" (instance $theory
        (export "var"       (func (result s32)))
        (export "plus"      (func (param "a" s32) (param "b" s32) (result s32)))
        (export "assoc"     (func (param "lhs" s32) (param "rhs" s32)))
        (export "verify-eq" (func (param "a" s32) (param "b" s32)))
    ))

    (alias export $theory "var"       (func $th_var))
    (alias export $theory "plus"      (func $th_plus))
    (alias export $theory "assoc"     (func $th_assoc))
    (alias export $theory "verify-eq" (func $th_verify_eq))

    (core module $m
        (import "env" "var"       (func $var (result i32)))
        (import "env" "plus"      (func $plus (param i32 i32) (result i32)))
        (import "env" "assoc"     (func $assoc (param i32 i32)))
        (import "env" "verify-eq" (func $verify_eq (param i32 i32)))

        (global $x   (mut i32) (i32.const 0))
        (global $y   (mut i32) (i32.const 0))
        (global $z   (mut i32) (i32.const 0))
        (global $lhs (mut i32) (i32.const 0))
        (global $rhs (mut i32) (i32.const 0))

        (func $start
            (global.set $x (call $var))
            (global.set $y (call $var))
            (global.set $z (call $var))
            ;; lhs = (x + y) + z
            (global.set $lhs
                (call $plus
                    (call $plus (global.get $x) (global.get $y))
                    (global.get $z)))
            ;; rhs = x + (y + z)
            (global.set $rhs
                (call $plus
                    (global.get $x)
                    (call $plus (global.get $y) (global.get $z)))))
        (start $start)

        (func $get_x   (result i32) (global.get $x))
        (func $get_y   (result i32) (global.get $y))
        (func $get_z   (result i32) (global.get $z))
        (func $get_lhs (result i32) (global.get $lhs))
        (func $get_rhs (result i32) (global.get $rhs))
        (func $verify
            (call $verify_eq (global.get $lhs) (global.get $rhs)))

        ;; Forwarding functions to re-export theory through this component
        (func $fwd_var (result i32) (call $var))
        (func $fwd_plus (param $a i32) (param $b i32) (result i32)
            (call $plus (local.get $a) (local.get $b)))
        (func $fwd_assoc (param $a i32) (param $b i32)
            (call $assoc (local.get $a) (local.get $b)))
        (func $fwd_verify_eq (param $a i32) (param $b i32)
            (call $verify_eq (local.get $a) (local.get $b)))

        (export "get-x"     (func $get_x))
        (export "get-y"     (func $get_y))
        (export "get-z"     (func $get_z))
        (export "get-lhs"   (func $get_lhs))
        (export "get-rhs"   (func $get_rhs))
        (export "verify"    (func $verify))
        (export "var"       (func $fwd_var))
        (export "plus"      (func $fwd_plus))
        (export "assoc"     (func $fwd_assoc))
        (export "verify-eq" (func $fwd_verify_eq))
    )

    (core func $var_l       (canon lower (func $th_var)))
    (core func $plus_l      (canon lower (func $th_plus)))
    (core func $assoc_l     (canon lower (func $th_assoc)))
    (core func $verify_eq_l (canon lower (func $th_verify_eq)))

    (core instance $i (instantiate $m
        (with "env" (instance
            (export "var"       (func $var_l))
            (export "plus"      (func $plus_l))
            (export "assoc"     (func $assoc_l))
            (export "verify-eq" (func $verify_eq_l))
        ))
    ))

    (func $f_get_x   (result s32) (canon lift (core func $i "get-x")))
    (func $f_get_y   (result s32) (canon lift (core func $i "get-y")))
    (func $f_get_z   (result s32) (canon lift (core func $i "get-z")))
    (func $f_get_lhs (result s32) (canon lift (core func $i "get-lhs")))
    (func $f_get_rhs (result s32) (canon lift (core func $i "get-rhs")))
    (func $f_verify  (canon lift (core func $i "verify")))
    (func $f_var       (result s32) (canon lift (core func $i "var")))
    (func $f_plus      (param "a" s32) (param "b" s32) (result s32)
        (canon lift (core func $i "plus")))
    (func $f_assoc     (param "lhs" s32) (param "rhs" s32)
        (canon lift (core func $i "assoc")))
    (func $f_verify_eq (param "a" s32) (param "b" s32)
        (canon lift (core func $i "verify-eq")))

    (export "get-x"     (func $f_get_x))
    (export "get-y"     (func $f_get_y))
    (export "get-z"     (func $f_get_z))
    (export "get-lhs"   (func $f_get_lhs))
    (export "get-rhs"   (func $f_get_rhs))
    (export "verify"    (func $f_verify))
    (export "var"       (func $f_var))
    (export "plus"      (func $f_plus))
    (export "assoc"     (func $f_assoc))
    (export "verify-eq" (func $f_verify_eq))
)
