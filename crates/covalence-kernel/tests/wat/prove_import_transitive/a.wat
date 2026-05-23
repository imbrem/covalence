(component
    (import "prove-{b_hex}" (instance $b
        (export "trigger" (func))
    ))
    (alias export $b "trigger" (func $trigger))
    (core module $m
        (import "env" "trigger" (func $trigger))
        (func $start (call $trigger))
        (start $start)
    )
    (core func $trigger_lowered (canon lower (func $trigger)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "trigger" (func $trigger_lowered))
        ))
    ))
)
