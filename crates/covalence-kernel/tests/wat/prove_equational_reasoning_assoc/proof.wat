(component
    (import "prove-{prop_hex}" (instance $prop
        (export "get-lhs" (func (result s32)))
        (export "get-rhs" (func (result s32)))
        (export "assoc"   (func (param "lhs" s32) (param "rhs" s32)))
        (export "verify"  (func))
    ))

    (alias export $prop "get-lhs" (func $get_lhs))
    (alias export $prop "get-rhs" (func $get_rhs))
    (alias export $prop "assoc"   (func $assoc))
    (alias export $prop "verify"  (func $verify))

    (core module $m
        (import "env" "get-lhs" (func $get_lhs (result i32)))
        (import "env" "get-rhs" (func $get_rhs (result i32)))
        (import "env" "assoc"   (func $assoc (param i32 i32)))
        (import "env" "verify"  (func $verify))

        (func $start
            (local $lhs i32) (local $rhs i32)
            (local.set $lhs (call $get_lhs))
            (local.set $rhs (call $get_rhs))
            (call $assoc (local.get $lhs) (local.get $rhs))
            (call $verify))
        (start $start)
    )

    (core func $get_lhs_l (canon lower (func $get_lhs)))
    (core func $get_rhs_l (canon lower (func $get_rhs)))
    (core func $assoc_l   (canon lower (func $assoc)))
    (core func $verify_l  (canon lower (func $verify)))

    (core instance $i (instantiate $m
        (with "env" (instance
            (export "get-lhs" (func $get_lhs_l))
            (export "get-rhs" (func $get_rhs_l))
            (export "assoc"   (func $assoc_l))
            (export "verify"  (func $verify_l))
        ))
    ))
)
