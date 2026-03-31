(module
  (func $add (export "add") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add)
  (func $sub (export "sub") (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.sub)
  (memory (export "memory") 1)
  (global $counter (mut i32) (i32.const 0))
  (func $increment (export "increment") (result i32)
    global.get $counter
    i32.const 1
    i32.add
    global.set $counter
    global.get $counter)
  (@custom "build-info" "covalence-test-v1"))
