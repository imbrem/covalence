(component
    (core module $m
        (memory $parent 1)
        (memory $rank 1)
        (global $next_id (mut i32) (i32.const 0))

        (func $make (result i32)
            (local $id i32)
            (local.set $id (global.get $next_id))
            (global.set $next_id (i32.add (local.get $id) (i32.const 1)))
            (i32.store $parent
                (i32.mul (local.get $id) (i32.const 4))
                (local.get $id))
            (i32.store $rank
                (i32.mul (local.get $id) (i32.const 4))
                (i32.const 0))
            (local.get $id))

        (func $find (param $x i32) (result i32)
            (local $p i32)
            (local.set $p
                (i32.load $parent (i32.mul (local.get $x) (i32.const 4))))
            (if (result i32) (i32.ne (local.get $p) (local.get $x))
                (then
                    (local.set $p (call $find (local.get $p)))
                    (i32.store $parent
                        (i32.mul (local.get $x) (i32.const 4))
                        (local.get $p))
                    (local.get $p))
                (else (local.get $x))))

        (func $union (param $a i32) (param $b i32)
            (local $fa i32) (local $fb i32)
            (local $ra i32) (local $rb i32)
            (local.set $fa (call $find (local.get $a)))
            (local.set $fb (call $find (local.get $b)))
            (if (i32.ne (local.get $fa) (local.get $fb))
                (then
                    (local.set $ra (i32.load $rank
                        (i32.mul (local.get $fa) (i32.const 4))))
                    (local.set $rb (i32.load $rank
                        (i32.mul (local.get $fb) (i32.const 4))))
                    (if (i32.lt_s (local.get $ra) (local.get $rb))
                        (then
                            (i32.store $parent
                                (i32.mul (local.get $fa) (i32.const 4))
                                (local.get $fb)))
                        (else
                            (i32.store $parent
                                (i32.mul (local.get $fb) (i32.const 4))
                                (local.get $fa))
                            (if (i32.eq (local.get $ra) (local.get $rb))
                                (then
                                    (i32.store $rank
                                        (i32.mul (local.get $fa) (i32.const 4))
                                        (i32.add (local.get $ra) (i32.const 1))))))))))

        (export "make" (func $make))
        (export "find" (func $find))
        (export "union" (func $union))
    )
    (core instance $i (instantiate $m))
    (func $make (result s32) (canon lift (core func $i "make")))
    (func $find (param "x" s32) (result s32) (canon lift (core func $i "find")))
    (func $union (param "a" s32) (param "b" s32) (canon lift (core func $i "union")))
    (export "make" (func $make))
    (export "find" (func $find))
    (export "union" (func $union))
)
