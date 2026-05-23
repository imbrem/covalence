(component
    (import "prove-{c_hex}" (instance $c
        (export "go" (func))
    ))
    (alias export $c "go" (func $c_go))
    (core module $m
        (import "env" "c_go" (func $c_go))
        (func $trigger (call $c_go))
        (export "trigger" (func $trigger))
    )
    (core func $c_go_lowered (canon lower (func $c_go)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "c_go" (func $c_go_lowered))
        ))
    ))
    (func $trigger (canon lift (core func $i "trigger")))
    (export "trigger" (func $trigger))
)
