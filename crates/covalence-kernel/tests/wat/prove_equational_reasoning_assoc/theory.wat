(component
    (import "attest" (func $attest))
    (import "component-{uf_hex}" (instance $uf
        (export "make" (func (result s32)))
        (export "find" (func (param "x" s32) (result s32)))
        (export "union" (func (param "a" s32) (param "b" s32)))
    ))
    (import "component-{map_hex}" (instance $map
        (export "lookup" (func (param "a" s32) (param "b" s32) (result s32)))
        (export "insert" (func (param "a" s32) (param "b" s32) (param "val" s32)))
    ))

    (alias export $uf "make" (func $uf_make))
    (alias export $uf "find" (func $uf_find))
    (alias export $uf "union" (func $uf_union))
    (alias export $map "lookup" (func $map_lookup))
    (alias export $map "insert" (func $map_insert))

    (core module $m
        (import "env" "make"   (func $make   (result i32)))
        (import "env" "find"   (func $find   (param i32) (result i32)))
        (import "env" "union"  (func $union  (param i32 i32)))
        (import "env" "lookup" (func $lookup (param i32 i32) (result i32)))
        (import "env" "insert" (func $insert (param i32 i32 i32)))
        (import "env" "attest" (func $attest))

        (memory $tags   1)
        (memory $lefts  1)
        (memory $rights 1)

        ;; var() -> id
        (func $var (result i32)
            (local $id i32)
            (local.set $id (call $make))
            (i32.store $tags
                (i32.mul (local.get $id) (i32.const 4)) (i32.const 0))
            (local.get $id))

        ;; plus(a, b) -> id  (hash-consed via map)
        (func $plus (param $a i32) (param $b i32) (result i32)
            (local $fa i32) (local $fb i32)
            (local $existing i32) (local $id i32)
            (local.set $fa (call $find (local.get $a)))
            (local.set $fb (call $find (local.get $b)))
            (local.set $existing
                (call $lookup (local.get $fa) (local.get $fb)))
            (if (result i32)
                (i32.ne (local.get $existing) (i32.const -1))
                (then (local.get $existing))
                (else
                    (local.set $id (call $make))
                    (i32.store $tags
                        (i32.mul (local.get $id) (i32.const 4))
                        (i32.const 1))
                    (i32.store $lefts
                        (i32.mul (local.get $id) (i32.const 4))
                        (local.get $a))
                    (i32.store $rights
                        (i32.mul (local.get $id) (i32.const 4))
                        (local.get $b))
                    (call $insert
                        (local.get $fa) (local.get $fb) (local.get $id))
                    (local.get $id))))

        ;; assoc(lhs, rhs): verify structure matches and union
        ;; lhs = (A+B)+C,  rhs = A+(B+C)
        (func $assoc (param $lhs i32) (param $rhs i32)
            (local $ab i32) (local $c_l i32)
            (local $a_l i32) (local $b_l i32)
            (local $a_r i32) (local $bc i32)
            (local $b_r i32) (local $c_r i32)
            ;; decompose lhs = AB + C
            (local.set $ab
                (i32.load $lefts
                    (i32.mul (local.get $lhs) (i32.const 4))))
            (local.set $c_l
                (i32.load $rights
                    (i32.mul (local.get $lhs) (i32.const 4))))
            ;; decompose AB = A + B
            (local.set $a_l
                (i32.load $lefts
                    (i32.mul (local.get $ab) (i32.const 4))))
            (local.set $b_l
                (i32.load $rights
                    (i32.mul (local.get $ab) (i32.const 4))))
            ;; decompose rhs = A + BC
            (local.set $a_r
                (i32.load $lefts
                    (i32.mul (local.get $rhs) (i32.const 4))))
            (local.set $bc
                (i32.load $rights
                    (i32.mul (local.get $rhs) (i32.const 4))))
            ;; decompose BC = B + C
            (local.set $b_r
                (i32.load $lefts
                    (i32.mul (local.get $bc) (i32.const 4))))
            (local.set $c_r
                (i32.load $rights
                    (i32.mul (local.get $bc) (i32.const 4))))
            ;; check find(A_l)==find(A_r), find(B_l)==find(B_r), find(C_l)==find(C_r)
            (if (i32.and
                    (i32.and
                        (i32.eq (call $find (local.get $a_l))
                                (call $find (local.get $a_r)))
                        (i32.eq (call $find (local.get $b_l))
                                (call $find (local.get $b_r))))
                    (i32.eq (call $find (local.get $c_l))
                            (call $find (local.get $c_r))))
                (then (call $union (local.get $lhs) (local.get $rhs)))
                (else (unreachable))))

        ;; verify-eq(a, b): attest if find(a)==find(b), else trap
        (func $verify_eq (param $a i32) (param $b i32)
            (if (i32.eq (call $find (local.get $a))
                        (call $find (local.get $b)))
                (then (call $attest))
                (else (unreachable))))

        (export "var"       (func $var))
        (export "plus"      (func $plus))
        (export "assoc"     (func $assoc))
        (export "verify-eq" (func $verify_eq))
    )

    (core func $make_l   (canon lower (func $uf_make)))
    (core func $find_l   (canon lower (func $uf_find)))
    (core func $union_l  (canon lower (func $uf_union)))
    (core func $lookup_l (canon lower (func $map_lookup)))
    (core func $insert_l (canon lower (func $map_insert)))
    (core func $attest_l (canon lower (func $attest)))

    (core instance $i (instantiate $m
        (with "env" (instance
            (export "make"   (func $make_l))
            (export "find"   (func $find_l))
            (export "union"  (func $union_l))
            (export "lookup" (func $lookup_l))
            (export "insert" (func $insert_l))
            (export "attest" (func $attest_l))
        ))
    ))

    (func $e_var (result s32)
        (canon lift (core func $i "var")))
    (func $e_plus (param "a" s32) (param "b" s32) (result s32)
        (canon lift (core func $i "plus")))
    (func $e_assoc (param "lhs" s32) (param "rhs" s32)
        (canon lift (core func $i "assoc")))
    (func $e_verify_eq (param "a" s32) (param "b" s32)
        (canon lift (core func $i "verify-eq")))

    (export "var"       (func $e_var))
    (export "plus"      (func $e_plus))
    (export "assoc"     (func $e_assoc))
    (export "verify-eq" (func $e_verify_eq))
)
