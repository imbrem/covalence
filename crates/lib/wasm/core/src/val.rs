use std::fmt;

/// Named resource type — extension point for future serialization.
///
/// When a component exposes `serialize`/`deserialize` functions for a resource,
/// the `serialized_type` field (future) will describe the portable value type
/// that the resource serializes to/from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResourceType {
    pub name: String,
    // Future: pub serialized_type: Option<Box<ValType>>
}

/// Describes the shape of a component model value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValType {
    // Primitives
    Bool,
    S8,
    U8,
    S16,
    U16,
    S32,
    U32,
    S64,
    U64,
    F32,
    F64,
    V128,
    Char,
    String,
    // Compound
    List(Box<ValType>),
    Record(Vec<(std::string::String, ValType)>),
    Tuple(Vec<ValType>),
    Variant(Vec<(std::string::String, Option<ValType>)>),
    Enum(Vec<std::string::String>),
    Option(Box<ValType>),
    Result {
        ok: Option<Box<ValType>>,
        err: Option<Box<ValType>>,
    },
    Flags(Vec<std::string::String>),
    Resource(ResourceType),
}

/// Concrete component model value.
#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Bool(bool),
    S8(i8),
    U8(u8),
    S16(i16),
    U16(u16),
    S32(i32),
    U32(u32),
    S64(i64),
    U64(u64),
    F32(f32),
    F64(f64),
    V128(u128),
    Char(char),
    String(std::string::String),
    List(Vec<Val>),
    Record(Vec<(std::string::String, Val)>),
    Tuple(Vec<Val>),
    Variant {
        case: std::string::String,
        payload: Option<Box<Val>>,
    },
    Enum(std::string::String),
    Option(Option<Box<Val>>),
    Result(Result<Option<Box<Val>>, Option<Box<Val>>>),
    Flags(Vec<std::string::String>),
}

impl Val {
    /// Infer the structural type of this value.
    ///
    /// Note: for `Variant`, `Enum`, and `Flags` the inferred type only includes
    /// the single case/flag present in the value. Use `conforms_to` against a
    /// declared `ValType` for full type checking.
    pub fn val_type(&self) -> ValType {
        match self {
            Val::Bool(_) => ValType::Bool,
            Val::S8(_) => ValType::S8,
            Val::U8(_) => ValType::U8,
            Val::S16(_) => ValType::S16,
            Val::U16(_) => ValType::U16,
            Val::S32(_) => ValType::S32,
            Val::U32(_) => ValType::U32,
            Val::S64(_) => ValType::S64,
            Val::U64(_) => ValType::U64,
            Val::F32(_) => ValType::F32,
            Val::F64(_) => ValType::F64,
            Val::V128(_) => ValType::V128,
            Val::Char(_) => ValType::Char,
            Val::String(_) => ValType::String,
            Val::List(items) => {
                let elem = items.first().map(|v| v.val_type()).unwrap_or(ValType::Bool);
                ValType::List(Box::new(elem))
            }
            Val::Record(fields) => ValType::Record(
                fields
                    .iter()
                    .map(|(k, v)| (k.clone(), v.val_type()))
                    .collect(),
            ),
            Val::Tuple(items) => ValType::Tuple(items.iter().map(|v| v.val_type()).collect()),
            Val::Variant { case, payload } => {
                ValType::Variant(vec![(case.clone(), payload.as_ref().map(|v| v.val_type()))])
            }
            Val::Enum(case) => ValType::Enum(vec![case.clone()]),
            Val::Option(inner) => {
                let elem = inner
                    .as_ref()
                    .map(|v| v.val_type())
                    .unwrap_or(ValType::Bool);
                ValType::Option(Box::new(elem))
            }
            Val::Result(r) => {
                let ok = match r {
                    Ok(Some(v)) => Some(Box::new(v.val_type())),
                    _ => None,
                };
                let err = match r {
                    Err(Some(v)) => Some(Box::new(v.val_type())),
                    _ => None,
                };
                ValType::Result { ok, err }
            }
            Val::Flags(flags) => ValType::Flags(flags.clone()),
        }
    }

    /// Check whether this value conforms to the given type.
    ///
    /// For enum/variant/flags types, checks that names in the value are valid
    /// members of the declared type. For records, checks field names and types
    /// match exactly.
    pub fn conforms_to(&self, ty: &ValType) -> bool {
        match (self, ty) {
            (Val::Bool(_), ValType::Bool) => true,
            (Val::S8(_), ValType::S8) => true,
            (Val::U8(_), ValType::U8) => true,
            (Val::S16(_), ValType::S16) => true,
            (Val::U16(_), ValType::U16) => true,
            (Val::S32(_), ValType::S32) => true,
            (Val::U32(_), ValType::U32) => true,
            (Val::S64(_), ValType::S64) => true,
            (Val::U64(_), ValType::U64) => true,
            (Val::F32(_), ValType::F32) => true,
            (Val::F64(_), ValType::F64) => true,
            (Val::V128(_), ValType::V128) => true,
            (Val::Char(_), ValType::Char) => true,
            (Val::String(_), ValType::String) => true,

            (Val::List(items), ValType::List(elem_ty)) => {
                items.iter().all(|v| v.conforms_to(elem_ty))
            }

            (Val::Record(val_fields), ValType::Record(ty_fields)) => {
                if val_fields.len() != ty_fields.len() {
                    return false;
                }
                val_fields
                    .iter()
                    .zip(ty_fields.iter())
                    .all(|((vk, vv), (tk, tv))| vk == tk && vv.conforms_to(tv))
            }

            (Val::Tuple(val_items), ValType::Tuple(ty_items)) => {
                if val_items.len() != ty_items.len() {
                    return false;
                }
                val_items
                    .iter()
                    .zip(ty_items.iter())
                    .all(|(v, t)| v.conforms_to(t))
            }

            (Val::Variant { case, payload }, ValType::Variant(cases)) => {
                cases.iter().any(|(name, expected_payload)| {
                    name == case
                        && match (payload, expected_payload) {
                            (None, None) => true,
                            (Some(v), Some(t)) => v.conforms_to(t),
                            _ => false,
                        }
                })
            }

            (Val::Enum(case), ValType::Enum(cases)) => cases.contains(case),

            (Val::Option(inner), ValType::Option(elem_ty)) => match inner {
                None => true,
                Some(v) => v.conforms_to(elem_ty),
            },

            (Val::Result(r), ValType::Result { ok, err }) => match r {
                Ok(val) => match (val, ok) {
                    (None, None) => true,
                    (Some(v), Some(t)) => v.conforms_to(t),
                    (None, Some(_)) => false,
                    (Some(_), None) => false,
                },
                Err(val) => match (val, err) {
                    (None, None) => true,
                    (Some(v), Some(t)) => v.conforms_to(t),
                    (None, Some(_)) => false,
                    (Some(_), None) => false,
                },
            },

            (Val::Flags(flags), ValType::Flags(valid)) => flags.iter().all(|f| valid.contains(f)),

            _ => false,
        }
    }

    /// Short string describing this value's kind (e.g. "bool", "u32", "list").
    pub fn kind(&self) -> &'static str {
        match self {
            Val::Bool(_) => "bool",
            Val::S8(_) => "s8",
            Val::U8(_) => "u8",
            Val::S16(_) => "s16",
            Val::U16(_) => "u16",
            Val::S32(_) => "s32",
            Val::U32(_) => "u32",
            Val::S64(_) => "s64",
            Val::U64(_) => "u64",
            Val::F32(_) => "f32",
            Val::F64(_) => "f64",
            Val::V128(_) => "v128",
            Val::Char(_) => "char",
            Val::String(_) => "string",
            Val::List(_) => "list",
            Val::Record(_) => "record",
            Val::Tuple(_) => "tuple",
            Val::Variant { .. } => "variant",
            Val::Enum(_) => "enum",
            Val::Option(_) => "option",
            Val::Result(_) => "result",
            Val::Flags(_) => "flags",
        }
    }
}

impl ValType {
    /// Short string describing this type's kind (e.g. "bool", "u32", "list").
    pub fn kind(&self) -> &'static str {
        match self {
            ValType::Bool => "bool",
            ValType::S8 => "s8",
            ValType::U8 => "u8",
            ValType::S16 => "s16",
            ValType::U16 => "u16",
            ValType::S32 => "s32",
            ValType::U32 => "u32",
            ValType::S64 => "s64",
            ValType::U64 => "u64",
            ValType::F32 => "f32",
            ValType::F64 => "f64",
            ValType::V128 => "v128",
            ValType::Char => "char",
            ValType::String => "string",
            ValType::List(_) => "list",
            ValType::Record(_) => "record",
            ValType::Tuple(_) => "tuple",
            ValType::Variant(_) => "variant",
            ValType::Enum(_) => "enum",
            ValType::Option(_) => "option",
            ValType::Result { .. } => "result",
            ValType::Flags(_) => "flags",
            ValType::Resource(_) => "resource",
        }
    }
}

// -- Display impls -----------------------------------------------------------

impl fmt::Display for ValType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValType::Bool => write!(f, "bool"),
            ValType::S8 => write!(f, "s8"),
            ValType::U8 => write!(f, "u8"),
            ValType::S16 => write!(f, "s16"),
            ValType::U16 => write!(f, "u16"),
            ValType::S32 => write!(f, "s32"),
            ValType::U32 => write!(f, "u32"),
            ValType::S64 => write!(f, "s64"),
            ValType::U64 => write!(f, "u64"),
            ValType::F32 => write!(f, "f32"),
            ValType::F64 => write!(f, "f64"),
            ValType::V128 => write!(f, "v128"),
            ValType::Char => write!(f, "char"),
            ValType::String => write!(f, "string"),
            ValType::List(elem) => write!(f, "(list {elem})"),
            ValType::Record(fields) => {
                write!(f, "(record")?;
                for (name, ty) in fields {
                    write!(f, " (field \"{name}\" {ty})")?;
                }
                write!(f, ")")
            }
            ValType::Tuple(items) => {
                write!(f, "(tuple")?;
                for ty in items {
                    write!(f, " {ty}")?;
                }
                write!(f, ")")
            }
            ValType::Variant(cases) => {
                write!(f, "(variant")?;
                for (name, payload) in cases {
                    match payload {
                        Some(ty) => write!(f, " (case \"{name}\" {ty})")?,
                        None => write!(f, " (case \"{name}\")")?,
                    }
                }
                write!(f, ")")
            }
            ValType::Enum(cases) => {
                write!(f, "(enum")?;
                for name in cases {
                    write!(f, " \"{name}\"")?;
                }
                write!(f, ")")
            }
            ValType::Option(inner) => write!(f, "(option {inner})"),
            ValType::Result { ok, err } => {
                write!(f, "(result")?;
                if let Some(ok) = ok {
                    write!(f, " (ok {ok})")?;
                }
                if let Some(err) = err {
                    write!(f, " (error {err})")?;
                }
                write!(f, ")")
            }
            ValType::Flags(flags) => {
                write!(f, "(flags")?;
                for flag in flags {
                    write!(f, " \"{flag}\"")?;
                }
                write!(f, ")")
            }
            ValType::Resource(r) => write!(f, "(resource \"{}\")", r.name),
        }
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::Bool(v) => write!(f, "{v}"),
            Val::S8(v) => write!(f, "{v}"),
            Val::U8(v) => write!(f, "{v}"),
            Val::S16(v) => write!(f, "{v}"),
            Val::U16(v) => write!(f, "{v}"),
            Val::S32(v) => write!(f, "{v}"),
            Val::U32(v) => write!(f, "{v}"),
            Val::S64(v) => write!(f, "{v}"),
            Val::U64(v) => write!(f, "{v}"),
            Val::F32(v) => write!(f, "{v}"),
            Val::F64(v) => write!(f, "{v}"),
            Val::V128(v) => write!(f, "{v}"),
            Val::Char(v) => write!(f, "'{v}'"),
            Val::String(v) => write!(f, "\"{v}\""),
            Val::List(items) => {
                write!(f, "[")?;
                for (i, v) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Val::Record(fields) => {
                write!(f, "{{")?;
                for (i, (k, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{k}: {v}")?;
                }
                write!(f, "}}")
            }
            Val::Tuple(items) => {
                write!(f, "(")?;
                for (i, v) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, ")")
            }
            Val::Variant { case, payload } => match payload {
                Some(v) => write!(f, "{case}({v})"),
                None => write!(f, "{case}"),
            },
            Val::Enum(case) => write!(f, "{case}"),
            Val::Option(inner) => match inner {
                Some(v) => write!(f, "some({v})"),
                None => write!(f, "none"),
            },
            Val::Result(r) => match r {
                Ok(Some(v)) => write!(f, "ok({v})"),
                Ok(None) => write!(f, "ok"),
                Err(Some(v)) => write!(f, "err({v})"),
                Err(None) => write!(f, "err"),
            },
            Val::Flags(flags) => {
                write!(f, "{{")?;
                for (i, flag) in flags.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{flag}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitive_val_type() {
        assert_eq!(Val::Bool(true).val_type(), ValType::Bool);
        assert_eq!(Val::U32(42).val_type(), ValType::U32);
        assert_eq!(Val::S64(-1).val_type(), ValType::S64);
        assert_eq!(Val::F64(3.14).val_type(), ValType::F64);
        assert_eq!(Val::Char('x').val_type(), ValType::Char);
        assert_eq!(Val::String("hello".into()).val_type(), ValType::String);
    }

    #[test]
    fn list_val_type() {
        let list = Val::List(vec![Val::U32(1), Val::U32(2)]);
        assert_eq!(list.val_type(), ValType::List(Box::new(ValType::U32)));
    }

    #[test]
    fn empty_list_val_type() {
        let list = Val::List(vec![]);
        // Empty list defaults to bool element type
        assert_eq!(list.val_type(), ValType::List(Box::new(ValType::Bool)));
    }

    #[test]
    fn record_val_type() {
        let rec = Val::Record(vec![
            ("name".into(), Val::String("foo".into())),
            ("age".into(), Val::U32(42)),
        ]);
        assert_eq!(
            rec.val_type(),
            ValType::Record(vec![
                ("name".into(), ValType::String),
                ("age".into(), ValType::U32),
            ])
        );
    }

    #[test]
    fn tuple_val_type() {
        let tup = Val::Tuple(vec![Val::U32(1), Val::String("two".into())]);
        assert_eq!(
            tup.val_type(),
            ValType::Tuple(vec![ValType::U32, ValType::String])
        );
    }

    #[test]
    fn option_val_type() {
        let some = Val::Option(Some(Box::new(Val::U32(42))));
        assert_eq!(some.val_type(), ValType::Option(Box::new(ValType::U32)));

        let none = Val::Option(None);
        assert_eq!(none.val_type(), ValType::Option(Box::new(ValType::Bool)));
    }

    #[test]
    fn result_val_type() {
        let ok = Val::Result(Ok(Some(Box::new(Val::String("yes".into())))));
        assert_eq!(
            ok.val_type(),
            ValType::Result {
                ok: Some(Box::new(ValType::String)),
                err: None,
            }
        );

        let err = Val::Result(Err(Some(Box::new(Val::U32(1)))));
        assert_eq!(
            err.val_type(),
            ValType::Result {
                ok: None,
                err: Some(Box::new(ValType::U32)),
            }
        );
    }

    #[test]
    fn conforms_to_primitives() {
        assert!(Val::Bool(true).conforms_to(&ValType::Bool));
        assert!(Val::U32(42).conforms_to(&ValType::U32));
        assert!(!Val::U32(42).conforms_to(&ValType::S32));
        assert!(!Val::Bool(true).conforms_to(&ValType::U32));
    }

    #[test]
    fn conforms_to_list() {
        let ty = ValType::List(Box::new(ValType::U32));
        assert!(Val::List(vec![Val::U32(1), Val::U32(2)]).conforms_to(&ty));
        assert!(Val::List(vec![]).conforms_to(&ty));
        assert!(!Val::List(vec![Val::String("x".into())]).conforms_to(&ty));
    }

    #[test]
    fn conforms_to_record() {
        let ty = ValType::Record(vec![
            ("name".into(), ValType::String),
            ("age".into(), ValType::U32),
        ]);
        let good = Val::Record(vec![
            ("name".into(), Val::String("foo".into())),
            ("age".into(), Val::U32(42)),
        ]);
        assert!(good.conforms_to(&ty));

        // Wrong field name
        let bad = Val::Record(vec![
            ("nombre".into(), Val::String("foo".into())),
            ("age".into(), Val::U32(42)),
        ]);
        assert!(!bad.conforms_to(&ty));

        // Wrong field count
        let bad2 = Val::Record(vec![("name".into(), Val::String("foo".into()))]);
        assert!(!bad2.conforms_to(&ty));
    }

    #[test]
    fn conforms_to_variant() {
        let ty = ValType::Variant(vec![
            ("none".into(), None),
            ("some".into(), Some(ValType::U32)),
        ]);
        assert!(
            Val::Variant {
                case: "none".into(),
                payload: None,
            }
            .conforms_to(&ty)
        );
        assert!(
            Val::Variant {
                case: "some".into(),
                payload: Some(Box::new(Val::U32(42))),
            }
            .conforms_to(&ty)
        );
        assert!(
            !Val::Variant {
                case: "other".into(),
                payload: None,
            }
            .conforms_to(&ty)
        );
    }

    #[test]
    fn conforms_to_enum() {
        let ty = ValType::Enum(vec!["red".into(), "green".into(), "blue".into()]);
        assert!(Val::Enum("red".into()).conforms_to(&ty));
        assert!(!Val::Enum("yellow".into()).conforms_to(&ty));
    }

    #[test]
    fn conforms_to_flags() {
        let ty = ValType::Flags(vec!["read".into(), "write".into(), "execute".into()]);
        assert!(Val::Flags(vec!["read".into(), "write".into()]).conforms_to(&ty));
        assert!(Val::Flags(vec![]).conforms_to(&ty));
        assert!(!Val::Flags(vec!["delete".into()]).conforms_to(&ty));
    }

    #[test]
    fn conforms_to_option() {
        let ty = ValType::Option(Box::new(ValType::U32));
        assert!(Val::Option(None).conforms_to(&ty));
        assert!(Val::Option(Some(Box::new(Val::U32(42)))).conforms_to(&ty));
        assert!(!Val::Option(Some(Box::new(Val::String("x".into())))).conforms_to(&ty));
    }

    #[test]
    fn conforms_to_result() {
        let ty = ValType::Result {
            ok: Some(Box::new(ValType::String)),
            err: Some(Box::new(ValType::U32)),
        };
        assert!(Val::Result(Ok(Some(Box::new(Val::String("yes".into()))))).conforms_to(&ty));
        assert!(Val::Result(Err(Some(Box::new(Val::U32(1))))).conforms_to(&ty));
        assert!(!Val::Result(Ok(Some(Box::new(Val::U32(1))))).conforms_to(&ty));
    }

    #[test]
    fn display_primitives() {
        assert_eq!(ValType::Bool.to_string(), "bool");
        assert_eq!(ValType::U32.to_string(), "u32");
        assert_eq!(ValType::String.to_string(), "string");
    }

    #[test]
    fn display_compound() {
        assert_eq!(
            ValType::List(Box::new(ValType::U32)).to_string(),
            "(list u32)"
        );
        assert_eq!(
            ValType::Record(vec![
                ("name".into(), ValType::String),
                ("value".into(), ValType::U32),
            ])
            .to_string(),
            "(record (field \"name\" string) (field \"value\" u32))"
        );
        assert_eq!(
            ValType::Option(Box::new(ValType::U32)).to_string(),
            "(option u32)"
        );
        assert_eq!(
            ValType::Result {
                ok: Some(Box::new(ValType::String)),
                err: Some(Box::new(ValType::U32)),
            }
            .to_string(),
            "(result (ok string) (error u32))"
        );
    }

    #[test]
    fn display_val() {
        assert_eq!(Val::Bool(true).to_string(), "true");
        assert_eq!(Val::U32(42).to_string(), "42");
        assert_eq!(Val::String("hello".into()).to_string(), "\"hello\"");
        assert_eq!(
            Val::List(vec![Val::U32(1), Val::U32(2)]).to_string(),
            "[1, 2]"
        );
        assert_eq!(
            Val::Record(vec![("x".into(), Val::U32(1)), ("y".into(), Val::U32(2)),]).to_string(),
            "{x: 1, y: 2}"
        );
        assert_eq!(Val::Option(None).to_string(), "none");
        assert_eq!(
            Val::Option(Some(Box::new(Val::U32(42)))).to_string(),
            "some(42)"
        );
    }

    #[test]
    fn kind_strings() {
        assert_eq!(Val::Bool(true).kind(), "bool");
        assert_eq!(Val::U32(42).kind(), "u32");
        assert_eq!(Val::List(vec![]).kind(), "list");
        assert_eq!(ValType::Record(vec![]).kind(), "record");
        assert_eq!(
            ValType::Resource(ResourceType { name: "x".into() }).kind(),
            "resource"
        );
    }

    #[test]
    fn conforms_to_tuple() {
        let ty = ValType::Tuple(vec![ValType::U32, ValType::String]);
        assert!(Val::Tuple(vec![Val::U32(1), Val::String("two".into())]).conforms_to(&ty));
        assert!(!Val::Tuple(vec![Val::U32(1)]).conforms_to(&ty));
        assert!(
            !Val::Tuple(vec![Val::String("one".into()), Val::String("two".into())])
                .conforms_to(&ty)
        );
    }

    #[test]
    fn v128_val_type() {
        let v = Val::V128(42);
        assert_eq!(v.val_type(), ValType::V128);
        assert_eq!(v.kind(), "v128");
        assert!(v.conforms_to(&ValType::V128));
        assert!(!v.conforms_to(&ValType::U32));
    }

    #[test]
    fn v128_display() {
        assert_eq!(ValType::V128.to_string(), "v128");
        assert_eq!(Val::V128(0).to_string(), "0");
        assert_eq!(Val::V128(u128::MAX).to_string(), u128::MAX.to_string());
    }

    #[test]
    fn val_type_equality() {
        assert_eq!(ValType::U32, ValType::U32);
        assert_ne!(ValType::U32, ValType::S32);
        assert_eq!(
            ValType::List(Box::new(ValType::U32)),
            ValType::List(Box::new(ValType::U32))
        );
        assert_ne!(
            ValType::List(Box::new(ValType::U32)),
            ValType::List(Box::new(ValType::S32))
        );
    }
}
