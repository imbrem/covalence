(component
    (core module $m
        (type $entry (struct (field $a i32) (field $b i32) (field $val i32)))
        (type $table (array (mut (ref null $entry))))

        (global $tbl (mut (ref null $table)) (ref.null $table))
        (global $len (mut i32) (i32.const 0))

        (func $init
            (global.set $tbl
                (array.new $table (ref.null $entry) (i32.const 256))))
        (start $init)

        (func $lookup (param $a i32) (param $b i32) (result i32)
            (local $i i32)
            (local $e (ref null $entry))
            (block $out
                (loop $lp
                    (br_if $out (i32.ge_u (local.get $i) (global.get $len)))
                    (local.set $e
                        (array.get $table (global.get $tbl) (local.get $i)))
                    (if (i32.and
                            (i32.eq (struct.get $entry $a (local.get $e))
                                    (local.get $a))
                            (i32.eq (struct.get $entry $b (local.get $e))
                                    (local.get $b)))
                        (then
                            (return (struct.get $entry $val (local.get $e)))))
                    (local.set $i (i32.add (local.get $i) (i32.const 1)))
                    (br $lp)))
            (i32.const -1))

        (func $insert (param $a i32) (param $b i32) (param $val i32)
            (array.set $table (global.get $tbl) (global.get $len)
                (struct.new $entry
                    (local.get $a) (local.get $b) (local.get $val)))
            (global.set $len (i32.add (global.get $len) (i32.const 1))))

        (export "lookup" (func $lookup))
        (export "insert" (func $insert))
    )
    (core instance $i (instantiate $m))
    (func $lookup (param "a" s32) (param "b" s32) (result s32)
        (canon lift (core func $i "lookup")))
    (func $insert (param "a" s32) (param "b" s32) (param "val" s32)
        (canon lift (core func $i "insert")))
    (export "lookup" (func $lookup))
    (export "insert" (func $insert))
)
