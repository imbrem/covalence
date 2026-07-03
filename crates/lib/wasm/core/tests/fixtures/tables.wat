(module
  (type $return_i32 (func (result i32)))
  (table 2 funcref)
  (elem (i32.const 0) $f0 $f1)
  (func $f0 (type $return_i32) (i32.const 42))
  (func $f1 (type $return_i32) (i32.const 99))
  (func $call_indirect (export "call") (param $idx i32) (result i32)
    local.get $idx
    call_indirect (type $return_i32)))
