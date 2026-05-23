(component
    (import "link-{shared_hex}" (instance $shared
        (export "val" (func (result s32)))
    ))
    (import "prove-{dep_hex}" (instance $dep
        (export "noop" (func))
    ))
)
