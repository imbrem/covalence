(module
  (import "env" "log" (func $log (param i32)))
  (import "env" "memory" (memory 1))
  (func $greet (export "greet") (param $n i32)
    local.get $n
    call $log)
  (data (i32.const 0) "Hello, WebAssembly!\00")
  (@custom "source-map" "//# sourceMappingURL=test.map"))
