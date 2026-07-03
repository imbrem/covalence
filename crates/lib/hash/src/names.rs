use crate::O256;

macro_rules! standard_names {
    (
        root: $root:path;
        $($(#[$attr:meta])* $name:ident = $label:literal => [$($byte:expr),+ $(,)?]);+ $(;)?
    ) => {
        $($(#[$attr])* pub const $name: O256 = O256([$($byte),+]);)+

        #[cfg(test)]
        mod generated_tests {
            use super::*;
            use crate::HashCtx;

            #[test]
            fn all_standard_names_match_derivation() {
                let root = &$root;
                let names: &[(&str, &str, O256)] = &[
                    $((stringify!($name), $label, $name)),+
                ];
                for &(name, label, value) in names {
                    assert_eq!(value, root.tag(label),
                        "{name} does not match root.tag(\"{label}\")");
                }
            }
        }
    };
}

standard_names! {
    root: crate::COV_ROOT;

    /// Canonical SAT decision identifier: `COV_ROOT.tag("sat")`.
    SAT = "sat" => [
        0xc4, 0xfa, 0xb5, 0x20, 0xfc, 0x97, 0xd6, 0xd2,
        0xf1, 0x68, 0x66, 0x84, 0x77, 0xf6, 0xd2, 0x21,
        0x17, 0x03, 0x02, 0xc8, 0xdf, 0xef, 0x5b, 0xd8,
        0xda, 0x8e, 0x86, 0x64, 0x79, 0x61, 0x38, 0x01,
    ];

    /// Canonical UNSAT decision identifier: `COV_ROOT.tag("unsat")`.
    UNSAT = "unsat" => [
        0xfd, 0x04, 0x3b, 0xcc, 0xf2, 0x28, 0xd0, 0xd9,
        0xa3, 0x26, 0x65, 0x00, 0x8a, 0x52, 0x66, 0xf9,
        0x65, 0x56, 0xf6, 0x44, 0x66, 0x99, 0x09, 0x26,
        0x27, 0xbe, 0xf2, 0xcb, 0x04, 0x45, 0x42, 0x29,
    ]
}
