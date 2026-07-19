//! Ordered, theorem-neutral ACL2 world evaluation.
//!
//! This is an untrusted front-end utility for read-time constants and
//! `make-event` data.  It never admits a definition and never constructs a
//! theorem.

use std::collections::BTreeMap;

use covalence_sexp::{Atom, SExpr};
use covalence_types::Int;

use crate::acl2_api::{Acl2EventWorld, Acl2WorldView, WorldEventStatus};

/// A small ACL2 value universe sufficient for ordered read-time constants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorldValue {
    Nil,
    Int(Int),
    Symbol(String),
    String(Vec<u8>),
    /// Proper ACL2 lists use flat storage so large generated tables do not
    /// recurse through the Rust stack merely to clone or drop their spine.
    List(Vec<Self>),
    /// Genuine dotted pairs retain their structural representation.
    Cons(Box<Self>, Box<Self>),
}

/// Evaluated `make-event` data, retaining large quoted constant payloads in
/// their flat world representation when no surface syntax is needed.
pub enum GeneratedEventData {
    /// A generated `(progn (defconst NAME 'VALUE) ...)`.  This is the shape
    /// used to finalize x86isa's four opcode maps.
    QuotedDefconstProgn(Vec<(String, WorldValue)>),
    /// General generated events continue through the ordinary surface path.
    Surface(SExpr),
}

impl WorldValue {
    fn list(values: impl IntoIterator<Item = Self>) -> Self {
        let values = values.into_iter().collect::<Vec<_>>();
        if values.is_empty() {
            Self::Nil
        } else {
            Self::List(values)
        }
    }

    fn truth(value: bool) -> Self {
        if value {
            Self::Symbol("t".into())
        } else {
            Self::Nil
        }
    }

    fn is_true(&self) -> bool {
        !matches!(self, Self::Nil)
    }

    pub fn as_int(&self) -> Option<&Int> {
        match self {
            Self::Int(value) => Some(value),
            _ => None,
        }
    }

    /// Convert quoted/event data back to the surface representation.
    pub fn to_sexpr(&self) -> Result<SExpr, WorldError> {
        match self {
            Self::Nil => Ok(SExpr::list(vec![])),
            Self::Int(value) => Ok(SExpr::symbol(value.to_string())),
            Self::Symbol(value) => Ok(SExpr::symbol(value)),
            Self::String(value) => Ok(SExpr::string("", value.clone())),
            Self::List(values) => values
                .iter()
                .map(Self::to_sexpr)
                .collect::<Result<Vec<_>, _>>()
                .map(SExpr::list),
            Self::Cons(_, _) => {
                let mut values = Vec::new();
                let mut cursor = self;
                loop {
                    match cursor {
                        Self::Cons(head, tail) => {
                            values.push(head.to_sexpr()?);
                            cursor = tail;
                        }
                        Self::Nil => return Ok(SExpr::list(values)),
                        _ => {
                            values.push(SExpr::symbol("."));
                            values.push(cursor.to_sexpr()?);
                            return Ok(SExpr::list(values));
                        }
                    }
                }
            }
        }
    }
}

#[derive(Clone)]
struct WorldFunction {
    required: Vec<String>,
    keys: Vec<MacroKeyword>,
    body: SExpr,
}

#[derive(Clone)]
struct WorldMacro {
    required: Vec<String>,
    optional: Vec<MacroParameter>,
    rest: Option<String>,
    keys: Vec<MacroKeyword>,
    body: SExpr,
}

#[derive(Clone)]
struct DefineGuts {
    name: String,
    formals: Vec<String>,
    returns: Option<WorldValue>,
    has_triple_slash: bool,
}

#[derive(Clone)]
struct MacroParameter {
    name: String,
    default: Option<SExpr>,
    supplied: Option<String>,
}

#[derive(Clone)]
struct MacroKeyword {
    keyword: String,
    parameter: MacroParameter,
}

/// Ordered constants and read-time functions for one ACL2 book world.
#[derive(Default)]
pub struct Acl2World {
    constants: BTreeMap<String, WorldValue>,
    functions: BTreeMap<String, WorldFunction>,
    macros: BTreeMap<String, WorldMacro>,
    define_guts: BTreeMap<String, DefineGuts>,
    current_define: Option<String>,
    tables: BTreeMap<String, Vec<(WorldValue, WorldValue)>>,
    fuel: usize,
}

impl Acl2World {
    pub fn new() -> Self {
        Self {
            fuel: 100_000,
            ..Self::default()
        }
    }

    pub fn constant(&self, name: &str) -> Option<&WorldValue> {
        self.constants.get(name)
    }

    pub fn constants(&self) -> &BTreeMap<String, WorldValue> {
        &self.constants
    }

    /// Install already-evaluated generated constant data.
    ///
    /// This is deliberately data-only: it grants no logical authority and is
    /// used by the book pipeline only after recognizing a generated defconst.
    pub fn install_generated_constant(&mut self, name: String, value: WorldValue) {
        self.constants.insert(name, value);
    }

    /// Process an ordered event. Non-world events are reported as untouched.
    pub fn process_event(&mut self, event: &SExpr) -> Result<bool, WorldError> {
        let Some(items) = list(event) else {
            return Ok(false);
        };
        let Some(head) = items.first().and_then(symbol) else {
            return Ok(false);
        };
        match head {
            "defconst" => {
                if items.len() != 3 {
                    return Err(WorldError::Malformed("defconst"));
                }
                let name = symbol(&items[1]).ok_or(WorldError::Malformed("defconst name"))?;
                let value = self.eval_root(&items[2])?;
                self.constants.insert(name.into(), value);
                Ok(true)
            }
            "defconsts" => {
                if items.len() != 3 {
                    return Err(WorldError::Malformed("defconsts"));
                }
                let names = list(&items[1]).ok_or(WorldError::Malformed("defconsts names"))?;
                let values = proper_list(self.eval_root(&items[2])?)?;
                let values = values
                    .strip_prefix(&[WorldValue::Symbol("mv".into())])
                    .unwrap_or(&values);
                if names.len() != values.len() {
                    return Err(WorldError::Arity("defconsts"));
                }
                for (name, value) in names.iter().zip(values) {
                    self.constants.insert(
                        symbol(name)
                            .ok_or(WorldError::Malformed("defconsts name"))?
                            .into(),
                        value.clone(),
                    );
                }
                Ok(true)
            }
            "defun" | "defund" => {
                if items.len() < 4 {
                    return Err(WorldError::Malformed("defun"));
                }
                let name = symbol(&items[1]).ok_or(WorldError::Malformed("defun name"))?;
                let required = list(&items[2])
                    .ok_or(WorldError::Malformed("defun formals"))?
                    .iter()
                    .map(|formal| {
                        symbol(formal)
                            .map(str::to_owned)
                            .ok_or(WorldError::Malformed("defun formal"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let body = items[3..]
                    .iter()
                    .rev()
                    .find(|form| !is_declare(form))
                    .ok_or(WorldError::Malformed("defun body"))?
                    .clone();
                self.functions.insert(
                    name.into(),
                    WorldFunction {
                        required,
                        keys: vec![],
                        body,
                    },
                );
                Ok(true)
            }
            "define" => {
                if items.len() < 4 {
                    return Err(WorldError::Malformed("define"));
                }
                let name = symbol(&items[1]).ok_or(WorldError::Malformed("define name"))?;
                let lambda = list(&items[2]).ok_or(WorldError::Malformed("define formals"))?;
                let (required, optional, rest, keys) = macro_lambda_list(lambda)?;
                if !optional.is_empty() || rest.is_some() {
                    return Err(WorldError::UnsupportedMacro(
                        "read-time define supports required and &key formals".into(),
                    ));
                }
                let mut cursor = 3;
                while let Some(form) = items.get(cursor) {
                    if matches!(form, SExpr::Atom(Atom::Str { .. })) || is_declare(form) {
                        cursor += 1;
                    } else {
                        break;
                    }
                }
                while items
                    .get(cursor)
                    .and_then(symbol)
                    .is_some_and(|name| name.starts_with(':'))
                {
                    cursor += 2;
                }
                let body = items
                    .get(cursor)
                    .ok_or(WorldError::Malformed("define body"))?
                    .clone();
                let triple_slash = items.iter().position(|form| symbol(form) == Some("///"));
                let metadata_end = triple_slash.unwrap_or(items.len());
                let returns = items[3..metadata_end]
                    .windows(2)
                    .find(|pair| symbol(&pair[0]) == Some(":returns"))
                    .map(|pair| quote(&pair[1]))
                    .transpose()?;
                let formals = required
                    .iter()
                    .cloned()
                    .chain(keys.iter().map(|key| key.parameter.name.clone()))
                    .collect::<Vec<_>>();
                self.functions.insert(
                    name.into(),
                    WorldFunction {
                        required,
                        keys,
                        body,
                    },
                );
                self.define_guts.insert(
                    name.into(),
                    DefineGuts {
                        name: name.into(),
                        formals,
                        returns,
                        has_triple_slash: triple_slash.is_some(),
                    },
                );
                self.current_define = Some(name.into());
                Ok(true)
            }
            "defmacro" => {
                if items.len() < 4 {
                    return Err(WorldError::Malformed("defmacro"));
                }
                let name = symbol(&items[1]).ok_or(WorldError::Malformed("defmacro name"))?;
                let lambda =
                    list(&items[2]).ok_or(WorldError::Malformed("defmacro lambda list"))?;
                let (required, optional, rest, keys) = macro_lambda_list(lambda)?;
                let body = items[3..]
                    .iter()
                    .rev()
                    .find(|form| {
                        !is_declare(form) && !matches!(form, SExpr::Atom(Atom::Str { .. }))
                    })
                    .ok_or(WorldError::Malformed("defmacro body"))?
                    .clone();
                if !is_macro_template_body(&body) {
                    return Err(WorldError::UnsupportedMacro(
                        "computational bodies are not supported; expected a quasiquoted template or a simple conditional template".into(),
                    ));
                }
                self.macros.insert(
                    name.into(),
                    WorldMacro {
                        required,
                        optional,
                        rest,
                        keys,
                        body,
                    },
                );
                Ok(true)
            }
            "make-event" => {
                if items.len() != 2 {
                    return Err(WorldError::Malformed("make-event"));
                }
                let generated = self.eval_root(&items[1])?.to_sexpr()?;
                self.process_generated(&generated)?;
                Ok(true)
            }
            "table" => {
                if items.len() != 4 {
                    return Err(WorldError::UnsupportedTable(
                        "only concrete (table name key value) updates are supported".into(),
                    ));
                }
                let name = symbol(&items[1]).ok_or(WorldError::Malformed("table name"))?;
                let key = self.eval_root(&items[2])?;
                let value = self.eval_root(&items[3])?;
                let entries = self.tables.entry(name.into()).or_default();
                entries.retain(|(existing, _)| existing != &key);
                entries.insert(0, (key, value));
                Ok(true)
            }
            "local" if items.len() == 2 => self.process_event(&items[1]),
            "progn" => {
                for event in &items[1..] {
                    self.process_event(event)?;
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// Evaluate an explicit `(sharp-dot form)` and return replacement data.
    pub fn eval_sharp_dot(&mut self, form: &SExpr) -> Result<WorldValue, WorldError> {
        let items = list(form).ok_or(WorldError::Malformed("sharp-dot"))?;
        if items.len() != 2 || symbol(&items[0]) != Some("sharp-dot") {
            return Err(WorldError::Malformed("sharp-dot"));
        }
        self.eval_root(&items[1])
    }

    /// Evaluate a `(make-event expression)` to the event data it emits.
    ///
    /// This does not install the generated event; callers retain control over
    /// provenance, classification, and recursive event processing.
    pub fn eval_make_event(&mut self, form: &SExpr) -> Result<SExpr, WorldError> {
        match self.eval_make_event_data(form)? {
            GeneratedEventData::QuotedDefconstProgn(constants) => {
                let children = constants
                    .into_iter()
                    .map(|(name, value)| {
                        Ok(SExpr::list(vec![
                            SExpr::symbol("defconst"),
                            SExpr::symbol(name),
                            SExpr::list(vec![SExpr::symbol("quote"), value.to_sexpr()?]),
                        ]))
                    })
                    .collect::<Result<Vec<_>, WorldError>>()?;
                Ok(SExpr::list(
                    std::iter::once(SExpr::symbol("progn"))
                        .chain(children)
                        .collect::<Vec<_>>(),
                ))
            }
            GeneratedEventData::Surface(event) => Ok(event),
        }
    }

    /// Evaluate `make-event`, preserving giant generated quoted constants as
    /// flat [`WorldValue`] data instead of recursively materializing them as
    /// four quoted [`SExpr`] trees.
    pub fn eval_make_event_data(&mut self, form: &SExpr) -> Result<GeneratedEventData, WorldError> {
        let items = list(form).ok_or(WorldError::Malformed("make-event"))?;
        if items.len() != 2 || symbol(&items[0]) != Some("make-event") {
            return Err(WorldError::Malformed("make-event"));
        }
        if let Some(constants) = self.flat_opcode_map_finalizer(&items[1])? {
            return Ok(GeneratedEventData::QuotedDefconstProgn(constants));
        }
        let mut value = self.eval_root(&items[1])?;
        // ACL2 make-event permits the error/value/state convention in
        // addition to returning event data directly.
        if let WorldValue::List(values) = &mut value
            && values.len() == 3
            && values[0] == WorldValue::Nil
            && values[2] == WorldValue::Symbol("state".into())
        {
            value = std::mem::replace(&mut values[1], WorldValue::Nil);
        }
        match take_quoted_defconst_progn(value) {
            Ok(constants) => Ok(GeneratedEventData::QuotedDefconstProgn(constants)),
            Err(value) => Ok(GeneratedEventData::Surface(value.to_sexpr()?)),
        }
    }

    /// Recognize x86isa's generated opcode-map finalizer and retain its four
    /// maps in flat world storage.
    ///
    /// The ACL2 event runs `trans-eval` over every authored pre-map entry.
    /// Those entries are constructor calls whose world representation is
    /// already their resulting ACL2 data. Re-evaluating the recursive
    /// `eval-pre-map` walker would only rebuild the same list spine and can
    /// exhaust a bounded importer stack before any logical event is reached.
    /// This data-only shortcut has no theorem authority; the book pipeline
    /// records the ordinary generated-defconst provenance for every map.
    fn flat_opcode_map_finalizer(
        &self,
        expression: &SExpr,
    ) -> Result<Option<Vec<(String, WorldValue)>>, WorldError> {
        let Some(items) = list(expression) else {
            return Ok(None);
        };
        if items.first().and_then(symbol) != Some("mv-let") {
            return Ok(None);
        }
        let Some(bindings) = items.get(1).and_then(list) else {
            return Ok(None);
        };
        let expected_bindings = [
            "one-byte-opcode-map",
            "two-byte-opcode-map",
            "0f-38-three-byte-opcode-map",
            "0f-3a-three-byte-opcode-map",
            "state",
        ];
        if bindings.len() != expected_bindings.len()
            || !bindings
                .iter()
                .zip(expected_bindings)
                .all(|(binding, expected)| symbol(binding) == Some(expected))
        {
            return Ok(None);
        }

        let final_names = [
            "*one-byte-opcode-map*",
            "*two-byte-opcode-map*",
            "*0f-38-three-byte-opcode-map*",
            "*0f-3a-three-byte-opcode-map*",
        ];
        pre_opcode_map_names()
            .into_iter()
            .zip(final_names)
            .map(|(source, destination)| {
                self.constants
                    .get(source)
                    .cloned()
                    .map(|value| (destination.into(), value))
                    .ok_or_else(|| WorldError::Unbound(source.into()))
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Some)
    }

    /// Expand an ordinary registered macro call as untrusted event data.
    pub fn expand_macro_call(&mut self, form: &SExpr) -> Result<Option<SExpr>, WorldError> {
        let Some(items) = list(form) else {
            return Ok(None);
        };
        let Some(name) = items.first().and_then(symbol) else {
            return Ok(None);
        };
        let Some(definition) = self.macros.get(name).cloned() else {
            return Ok(None);
        };
        let arguments = &items[1..];
        if arguments.len() < definition.required.len()
            || (definition.rest.is_none()
                && definition.optional.is_empty()
                && definition.keys.is_empty()
                && arguments.len() != definition.required.len())
        {
            return Err(WorldError::MacroArity(name.into()));
        }
        let mut scope = BTreeMap::new();
        for (formal, argument) in definition.required.iter().zip(arguments) {
            scope.insert(formal.clone(), quote(argument)?);
        }
        let mut trailing = &arguments[definition.required.len()..];
        for optional in definition.optional {
            let present = trailing
                .first()
                .is_some_and(|argument| definition.keys.is_empty() || !is_keyword(argument));
            let value = if present {
                let value = quote(&trailing[0])?;
                trailing = &trailing[1..];
                value
            } else if let Some(default) = optional.default {
                self.eval(&default, &scope)?
            } else {
                WorldValue::Nil
            };
            scope.insert(optional.name, value);
            if let Some(supplied) = optional.supplied {
                scope.insert(supplied, WorldValue::truth(present));
            }
        }
        if let Some(rest) = definition.rest {
            let values = trailing.iter().map(quote).collect::<Result<Vec<_>, _>>()?;
            scope.insert(rest, WorldValue::list(values.into_iter()));
        }
        if !definition.keys.is_empty() {
            if trailing.len() % 2 != 0 {
                return Err(WorldError::MacroArity(name.into()));
            }
            let mut supplied = BTreeMap::new();
            for pair in trailing.chunks_exact(2) {
                let keyword = symbol(&pair[0])
                    .filter(|keyword| keyword.starts_with(':'))
                    .ok_or_else(|| {
                        WorldError::UnknownMacroKeyword(name.into(), format!("{:?}", pair[0]))
                    })?;
                let key = keyword.trim_start_matches(':');
                if supplied.insert(key.to_string(), quote(&pair[1])?).is_some() {
                    return Err(WorldError::DuplicateMacroKeyword(key.into()));
                }
            }
            for key in definition.keys {
                let present = supplied.contains_key(&key.keyword);
                let value = if let Some(value) = supplied.remove(&key.keyword) {
                    value
                } else if let Some(default) = key.parameter.default {
                    self.eval(&default, &scope)?
                } else {
                    WorldValue::Nil
                };
                scope.insert(key.parameter.name, value);
                if let Some(supplied) = key.parameter.supplied {
                    scope.insert(supplied, WorldValue::truth(present));
                }
            }
            if let Some(unknown) = supplied.keys().next() {
                return Err(WorldError::UnknownMacroKeyword(
                    name.into(),
                    unknown.clone(),
                ));
            }
        }
        self.fuel = 100_000;
        self.eval(&definition.body, &scope)
            .and_then(|value| value.to_sexpr())
            .map(Some)
    }

    fn eval_root(&mut self, expr: &SExpr) -> Result<WorldValue, WorldError> {
        self.fuel = 100_000;
        self.eval(expr, &BTreeMap::new())
    }

    fn process_generated(&mut self, event: &SExpr) -> Result<(), WorldError> {
        if symbol(list(event).and_then(|items| items.first()).unwrap_or(event)) == Some("progn") {
            for child in &list(event).expect("checked list")[1..] {
                self.process_event(child)?;
            }
        } else {
            self.process_event(event)?;
        }
        Ok(())
    }

    fn eval(
        &mut self,
        expr: &SExpr,
        locals: &BTreeMap<String, WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        if self.fuel == 0 {
            return Err(WorldError::Fuel);
        }
        self.fuel -= 1;
        match expr {
            SExpr::Atom(Atom::Symbol(value)) => {
                if value == "nil" {
                    Ok(WorldValue::Nil)
                } else if value == "t"
                    || value == "state"
                    || value.starts_with(':')
                    || acl2_character_byte(value).is_some()
                {
                    // ACL2 keywords are self-evaluating, as are T and NIL.
                    // STATE is the globally bound ACL2 world stobj in
                    // read-time/make-event evaluation.
                    Ok(WorldValue::Symbol(value.to_string()))
                } else if let Ok(value) = value.parse::<Int>() {
                    Ok(WorldValue::Int(value))
                } else if let Some(value) = locals
                    .get(value.as_str())
                    .or_else(|| self.constants.get(value.as_str()))
                {
                    Ok(value.clone())
                } else {
                    Err(WorldError::Unbound(value.to_string()))
                }
            }
            SExpr::Atom(Atom::Str { bytes, .. }) => Ok(WorldValue::String(bytes.to_vec())),
            SExpr::List(items) if items.is_empty() => Ok(WorldValue::Nil),
            SExpr::List(items) => {
                let head = symbol(&items[0]).ok_or(WorldError::Malformed("application head"))?;
                if items.len() == 3 && symbol(&items[1]) == Some(".") {
                    // The reader preserves dotted call syntax as `(fn . args)`.
                    // Its cdr is a list of argument forms, not one quoted
                    // argument. Evaluate each form exactly as an ordinary
                    // function call would.
                    let arguments = list(&items[2]).ok_or(WorldError::ImproperList)?;
                    let args = arguments
                        .iter()
                        .map(|argument| self.eval(argument, locals))
                        .collect::<Result<Vec<_>, _>>()?;
                    return self.apply(head, args);
                }
                match head {
                    "quote" if items.len() == 2 => self.quote_readtime(&items[1], locals),
                    "quasiquote" if items.len() == 2 => self.quasiquote(&items[1], locals),
                    "sharp-dot" if items.len() == 2 => self.eval(&items[1], locals),
                    "if" if items.len() == 4 => {
                        if self.eval(&items[1], locals)?.is_true() {
                            self.eval(&items[2], locals)
                        } else {
                            self.eval(&items[3], locals)
                        }
                    }
                    "cond" => {
                        for clause in &items[1..] {
                            let clause =
                                list(clause).ok_or(WorldError::Malformed("cond clause"))?;
                            if clause.is_empty() {
                                return Err(WorldError::Malformed("cond clause"));
                            }
                            let test = self.eval(&clause[0], locals)?;
                            if test.is_true() {
                                if clause.len() == 1 {
                                    return Ok(test);
                                }
                                let mut result = WorldValue::Nil;
                                for body in &clause[1..] {
                                    result = self.eval(body, locals)?;
                                }
                                return Ok(result);
                            }
                        }
                        Ok(WorldValue::Nil)
                    }
                    "case" if items.len() >= 2 => {
                        let key = self.eval(&items[1], locals)?;
                        for clause in &items[2..] {
                            let clause =
                                list(clause).ok_or(WorldError::Malformed("case clause"))?;
                            if clause.is_empty() {
                                return Err(WorldError::Malformed("case clause"));
                            }
                            let selector = &clause[0];
                            let default =
                                matches!(symbol(selector), Some("t" | "otherwise" | ":otherwise"));
                            let selected = if default {
                                true
                            } else if let Some(selectors) = list(selector) {
                                selectors
                                    .iter()
                                    .map(quote)
                                    .collect::<Result<Vec<_>, _>>()?
                                    .iter()
                                    .any(|selector| acl2_eql(selector, &key))
                            } else {
                                acl2_eql(&quote(selector)?, &key)
                            };
                            if selected {
                                let mut result = WorldValue::Nil;
                                for body in &clause[1..] {
                                    result = self.eval(body, locals)?;
                                }
                                return Ok(result);
                            }
                        }
                        Ok(WorldValue::Nil)
                    }
                    "let" | "let*" if items.len() >= 3 => {
                        let bindings =
                            list(&items[1]).ok_or(WorldError::Malformed("let bindings"))?;
                        let mut scope = locals.clone();
                        for binding in bindings {
                            let pair = list(binding).ok_or(WorldError::Malformed("let binding"))?;
                            if pair.len() != 2 {
                                return Err(WorldError::Malformed("let binding"));
                            }
                            let name = symbol(&pair[0]).ok_or(WorldError::Malformed("let name"))?;
                            let environment = if head == "let" { locals } else { &scope };
                            let value = self.eval(&pair[1], environment)?;
                            scope.insert(name.into(), value);
                        }
                        self.eval(items.last().expect("len checked"), &scope)
                    }
                    "b*" if items.len() >= 3 => self.eval_bstar(items, locals),
                    "mv-let" if items.len() >= 4 => self.eval_mv_let(items, locals),
                    "loop$" => self.eval_loop(items, locals),
                    "and" => {
                        let mut value = WorldValue::Symbol("t".into());
                        for item in &items[1..] {
                            value = self.eval(item, locals)?;
                            if !value.is_true() {
                                break;
                            }
                        }
                        Ok(value)
                    }
                    "or" => {
                        for item in &items[1..] {
                            let value = self.eval(item, locals)?;
                            if value.is_true() {
                                return Ok(value);
                            }
                        }
                        Ok(WorldValue::Nil)
                    }
                    "table-alist" if items.len() == 3 => {
                        let table = self.eval(&items[1], locals)?;
                        let WorldValue::Symbol(name) = table else {
                            return Err(WorldError::Malformed("table-alist name"));
                        };
                        let entries = self.tables.get(&name).cloned().unwrap_or_default();
                        Ok(WorldValue::list(entries.into_iter().map(|(key, value)| {
                            WorldValue::Cons(Box::new(key), Box::new(value))
                        })))
                    }
                    "find-insts-named"
                        if items.len() == 3
                            && list(&items[2])
                                .and_then(|call| call.first())
                                .and_then(symbol)
                                == Some("all-opcode-maps") =>
                    {
                        let names = proper_list(self.eval(&items[1], locals)?)?;
                        let mut found = Vec::new();
                        for map_name in [
                            "*pre-one-byte-opcode-map*",
                            "*pre-two-byte-opcode-map*",
                            "*pre-0f-38-three-byte-opcode-map*",
                            "*pre-0f-3a-three-byte-opcode-map*",
                        ] {
                            let entries = proper_list(
                                self.constants
                                    .get(map_name)
                                    .cloned()
                                    .ok_or_else(|| WorldError::Unbound(map_name.into()))?,
                            )?;
                            for inst in entries {
                                let fields = proper_list(inst.clone())?;
                                if let Some(mnemonic) = fields.get(1)
                                    && names.iter().any(|name| match (name, mnemonic) {
                                        (WorldValue::Symbol(left), WorldValue::String(right)) => {
                                            left.as_bytes().eq_ignore_ascii_case(right)
                                        }
                                        _ => false,
                                    })
                                {
                                    found.push(inst);
                                }
                            }
                        }
                        Ok(WorldValue::list(found.into_iter()))
                    }
                    _ => {
                        let args = items[1..]
                            .iter()
                            .map(|arg| self.eval(arg, locals))
                            .collect::<Result<Vec<_>, _>>()?;
                        self.apply(head, args)
                    }
                }
            }
        }
    }

    fn eval_bstar(
        &mut self,
        items: &[SExpr],
        locals: &BTreeMap<String, WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        let bindings = list(&items[1]).ok_or(WorldError::Malformed("b* bindings"))?;
        let mut scope = locals.clone();
        for binding in bindings {
            let pair = list(binding).ok_or_else(|| {
                WorldError::UnsupportedMacro(format!("unsupported b* binding `{binding:?}`"))
            })?;
            if let Some(pattern) = pair.first().and_then(list)
                && matches!(pattern.first().and_then(symbol), Some("when" | "unless"))
                && pattern.len() == 2
                && pair.len() >= 2
            {
                let condition = self.eval(&pattern[1], &scope)?.is_true();
                let is_unless = pattern.first().and_then(symbol) == Some("unless");
                if condition != is_unless {
                    let mut result = WorldValue::Nil;
                    for body in &pair[1..] {
                        result = self.eval(body, &scope)?;
                    }
                    return Ok(result);
                }
                continue;
            }
            // FTY aggregate binders may omit the value expression.  In
            // `((inst inst))`, for example, the second INST is both the
            // aggregate variable and the value to destructure.  Keep this
            // deliberately limited to aggregate binders whose concrete
            // read-time representation we know.
            if pair.len() == 1
                && let Some(pattern) = pair.first().and_then(list)
                && pattern.len() == 2
                && let (Some(kind), Some(name)) = (symbol(&pattern[0]), symbol(&pattern[1]))
            {
                let value = scope
                    .get(name)
                    .cloned()
                    .ok_or_else(|| WorldError::Unbound(name.into()))?;
                match kind {
                    "inst" => {
                        bind_bstar_inst(&mut scope, name, value)?;
                        continue;
                    }
                    "opcode" => {
                        bind_bstar_opcode(&mut scope, name, value)?;
                        continue;
                    }
                    "operands" => {
                        bind_bstar_operands(&mut scope, name, value)?;
                        continue;
                    }
                    _ => {}
                }
            }
            if pair.len() != 2 {
                return Err(WorldError::UnsupportedMacro(format!(
                    "unsupported b* binding arity `{binding:?}`"
                )));
            }
            if let Some(pattern) = list(&pair[0])
                && pattern.first().and_then(symbol) == Some("mv")
            {
                let values = proper_list(self.eval(&pair[1], &scope)?)?;
                if values.len() != pattern.len() - 1 {
                    return Err(WorldError::Arity("b* mv binding"));
                }
                for (name, value) in pattern[1..].iter().zip(values) {
                    let name = symbol(name).ok_or(WorldError::Malformed("b* mv name"))?;
                    let name = name.strip_prefix('?').unwrap_or(name);
                    if name != "-" {
                        scope.insert(name.into(), value);
                    }
                }
                continue;
            }
            if let Some(pattern) = list(&pair[0])
                && pattern.first().and_then(symbol) == Some("list*")
                && pattern.len() == 3
            {
                let value = self.eval(&pair[1], &scope)?;
                let (first, rest) = match value {
                    WorldValue::List(values) => {
                        let mut values = values.into_iter();
                        let first = values.next().unwrap_or(WorldValue::Nil);
                        (first, WorldValue::list(values))
                    }
                    WorldValue::Cons(first, rest) => (*first, *rest),
                    _ => (WorldValue::Nil, WorldValue::Nil),
                };
                for (formal, value) in pattern[1..].iter().zip([first, rest]) {
                    let name =
                        symbol(formal).ok_or(WorldError::Malformed("b* list* binder name"))?;
                    let name = name.strip_prefix('?').unwrap_or(name);
                    if name != "-" {
                        scope.insert(name.into(), value);
                    }
                }
                continue;
            }
            if let Some(pattern) = list(&pair[0])
                && pattern.first().and_then(symbol) == Some("inst")
                && pattern.len() == 2
            {
                let name = symbol(&pattern[1]).ok_or(WorldError::Malformed("b* inst name"))?;
                let value = self.eval(&pair[1], &scope)?;
                bind_bstar_inst(&mut scope, name, value)?;
                continue;
            }
            if let Some(pattern) = list(&pair[0])
                && pattern.first().and_then(symbol) == Some("opcode")
                && pattern.len() == 2
            {
                let name = symbol(&pattern[1]).ok_or(WorldError::Malformed("b* opcode name"))?;
                let value = self.eval(&pair[1], &scope)?;
                bind_bstar_opcode(&mut scope, name, value)?;
                continue;
            }
            if let Some(pattern) = list(&pair[0])
                && pattern.first().and_then(symbol) == Some("operands")
                && pattern.len() == 2
            {
                let name = symbol(&pattern[1]).ok_or(WorldError::Malformed("b* operands name"))?;
                let value = self.eval(&pair[1], &scope)?;
                bind_bstar_operands(&mut scope, name, value)?;
                continue;
            }
            if let Some(pattern) = list(&pair[0])
                && pattern.first().and_then(symbol) == Some("sdm-instruction-table-entry")
                && pattern.len() == 2
            {
                let name = symbol(&pattern[1])
                    .ok_or(WorldError::Malformed("b* instruction-table-entry name"))?;
                let value = self.eval(&pair[1], &scope)?;
                bind_sdm_instruction_table_entry(&mut scope, name, value)?;
                continue;
            }
            if let Some(pattern) = list(&pair[0])
                && pattern.first().and_then(symbol) == Some("cons")
                && pattern.len() == 3
            {
                let value = self.eval(&pair[1], &scope)?;
                bind_bstar_cons_pattern(&mut scope, &pattern[1], &pattern[2], value)?;
                continue;
            }
            let name = symbol(&pair[0]).ok_or(WorldError::Malformed("b* name"))?;
            let value = self.eval(&pair[1], &scope)?;
            // `?x` is b*'s "ignore if unused" spelling for the ordinary
            // variable `x`; it does not change the lexical binding name.
            let name = name.strip_prefix('?').unwrap_or(name);
            if name != "-" {
                scope.insert(name.into(), value);
            }
        }
        self.eval(items.last().expect("len checked"), &scope)
    }

    /// Materialize reader-time `#.` forms even when they occur beneath quote.
    ///
    /// The surface reader deliberately preserves `#.` as `(sharp-dot ...)` so
    /// that the ordered ACL2 world, rather than the parser, controls
    /// evaluation.  Common Lisp performs that evaluation before QUOTE is
    /// constructed, so a plain structural quote here would incorrectly turn
    /// `'( #.*constant* )` into a list containing syntax instead of the
    /// constant's value.
    fn quote_readtime(
        &mut self,
        expr: &SExpr,
        locals: &BTreeMap<String, WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        let Some(items) = list(expr) else {
            return quote(expr);
        };
        if items.first().and_then(symbol) == Some("sharp-dot") && items.len() == 2 {
            return self.eval(&items[1], locals);
        }
        items
            .iter()
            .map(|item| self.quote_readtime(item, locals))
            .collect::<Result<Vec<_>, _>>()
            .map(WorldValue::list)
    }

    fn eval_mv_let(
        &mut self,
        items: &[SExpr],
        locals: &BTreeMap<String, WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        let names = list(&items[1]).ok_or(WorldError::Malformed("mv-let formals"))?;
        let values = proper_list(self.eval(&items[2], locals)?)?;
        if names.len() != values.len() {
            return Err(WorldError::Arity("mv-let"));
        }
        let mut scope = locals.clone();
        for (name, value) in names.iter().zip(values) {
            let name = symbol(name).ok_or(WorldError::Malformed("mv-let formal"))?;
            let name = name.strip_prefix('?').unwrap_or(name);
            if name != "-" {
                scope.insert(name.into(), value);
            }
        }
        let mut result = WorldValue::Nil;
        for body in &items[3..] {
            result = self.eval(body, &scope)?;
        }
        Ok(result)
    }

    fn expand_defret(
        &self,
        theorem_name: &WorldValue,
        arguments: &WorldValue,
        disabled: bool,
    ) -> Result<WorldValue, WorldError> {
        let WorldValue::Symbol(theorem_name) = theorem_name else {
            return Err(WorldError::ExpectedSymbol(format!("{theorem_name:?}")));
        };
        let arguments = proper_list(arguments.clone())?;
        let conclusion = arguments
            .first()
            .cloned()
            .ok_or_else(|| WorldError::Raised("defret: no body".into()))?;
        if (arguments.len() - 1) % 2 != 0 {
            return Err(WorldError::Raised(
                "defret: malformed keyword arguments".into(),
            ));
        }
        let mut keywords = BTreeMap::new();
        for pair in arguments[1..].chunks_exact(2) {
            let WorldValue::Symbol(keyword) = &pair[0] else {
                return Err(WorldError::Raised("defret: expected keyword".into()));
            };
            keywords.insert(keyword.clone(), pair[1].clone());
        }
        let function_name = match keywords.get(":fn") {
            Some(WorldValue::Symbol(name)) => name.clone(),
            Some(value) => return Err(WorldError::ExpectedSymbol(format!("{value:?}"))),
            None => self
                .current_define
                .clone()
                .ok_or_else(|| WorldError::Raised("defret: no current define".into()))?,
        };
        let guts = self
            .define_guts
            .get(&function_name)
            .ok_or_else(|| WorldError::Raised(format!("No define-guts for {function_name}")))?;
        if !guts.has_triple_slash {
            return Err(WorldError::Raised(format!(
                "defret outside /// for {}",
                guts.name
            )));
        }
        let returns = guts
            .returns
            .as_ref()
            .ok_or_else(|| WorldError::Raised(format!("No return names for {}", guts.name)))?;
        let return_names = define_return_names(returns)?;
        let no_bind = keywords.get(":no-bind").is_some_and(WorldValue::is_true);
        let pre_bind = keywords
            .get(":pre-bind")
            .cloned()
            .unwrap_or(WorldValue::Nil);
        if pre_bind.is_true() {
            return Err(WorldError::UnsupportedMacro(
                "defret :pre-bind is not yet supported".into(),
            ));
        }
        let mut formula = conclusion;
        if !no_bind {
            let pattern = if return_names.len() == 1 {
                WorldValue::Symbol(format!("?{}", return_names[0]))
            } else {
                WorldValue::list(
                    std::iter::once(WorldValue::Symbol("mv".into())).chain(
                        return_names
                            .iter()
                            .map(|name| WorldValue::Symbol(format!("?{name}"))),
                    ),
                )
            };
            let call = WorldValue::list(
                std::iter::once(WorldValue::Symbol(function_name.clone()))
                    .chain(guts.formals.iter().cloned().map(WorldValue::Symbol)),
            );
            formula = WorldValue::list([
                WorldValue::Symbol("b*".into()),
                WorldValue::list([WorldValue::list([pattern, call])]),
                formula,
            ]);
        }
        if let Some(hypothesis) = keywords.get(":hyp") {
            if matches!(hypothesis, WorldValue::Symbol(value) if value == ":guard" || value == ":fguard")
            {
                return Err(WorldError::UnsupportedMacro(
                    "defret :hyp :guard/:fguard requires retained guard metadata".into(),
                ));
            }
            formula = WorldValue::list([
                WorldValue::Symbol("implies".into()),
                hypothesis.clone(),
                formula,
            ]);
        }
        let expanded_name = theorem_name
            .replace("<fn!>", &function_name)
            .replace("<fn>", &guts.name);
        let mut event = vec![
            WorldValue::Symbol(if disabled { "defthmd" } else { "defthm" }.into()),
            WorldValue::Symbol(expanded_name),
            formula,
        ];
        for keyword in [":hints", ":otf-flg", ":rule-classes"] {
            if let Some(value) = keywords.get(keyword) {
                event.push(WorldValue::Symbol(keyword.into()));
                event.push(value.clone());
            }
        }
        Ok(WorldValue::list(event))
    }

    fn expand_more_returns(&self, arguments: &WorldValue) -> Result<WorldValue, WorldError> {
        let mut arguments = proper_list(arguments.clone())?;
        if arguments.is_empty() {
            return Err(WorldError::Raised("more-returns: no arguments".into()));
        }
        let function_name = if let Some(WorldValue::Symbol(name)) = arguments.first() {
            let name = name.clone();
            arguments.remove(0);
            name
        } else {
            self.current_define
                .clone()
                .ok_or_else(|| WorldError::Raised("more-returns: no current define".into()))?
        };
        let guts = self
            .define_guts
            .get(&function_name)
            .ok_or_else(|| WorldError::Raised(format!("No define-guts for {function_name}")))?;
        if !guts.has_triple_slash {
            return Err(WorldError::Raised(format!(
                "more-returns outside /// for {}",
                guts.name
            )));
        }
        let original_returns = guts
            .returns
            .as_ref()
            .ok_or_else(|| WorldError::Raised(format!("No return names for {}", guts.name)))?;
        let original_names = define_return_names(original_returns)?;
        let call = WorldValue::list(
            std::iter::once(WorldValue::Symbol(function_name.clone()))
                .chain(guts.formals.iter().cloned().map(WorldValue::Symbol)),
        );
        let pattern = if original_names.len() == 1 {
            WorldValue::Symbol(format!("?{}", original_names[0]))
        } else {
            WorldValue::list(
                std::iter::once(WorldValue::Symbol("mv".into())).chain(
                    original_names
                        .iter()
                        .map(|name| WorldValue::Symbol(format!("?{name}"))),
                ),
            )
        };
        let mut events = vec![WorldValue::Symbol("progn".into())];
        for spec in arguments {
            let spec = proper_list(spec)?;
            if spec.len() < 2 || (spec.len() - 2) % 2 != 0 {
                return Err(WorldError::Malformed("more-returns spec"));
            }
            let WorldValue::Symbol(return_name) = &spec[0] else {
                return Err(WorldError::Malformed("more-returns name"));
            };
            if !original_names.contains(return_name) {
                return Err(WorldError::Raised(format!(
                    "No return value named {return_name} for {}",
                    guts.name
                )));
            }
            let mut keywords = BTreeMap::new();
            for pair in spec[2..].chunks_exact(2) {
                let WorldValue::Symbol(keyword) = &pair[0] else {
                    return Err(WorldError::Malformed("more-returns keyword"));
                };
                keywords.insert(keyword.clone(), pair[1].clone());
            }
            let theorem_name = match keywords.get(":name") {
                Some(WorldValue::Symbol(name)) => name.clone(),
                Some(value) => return Err(WorldError::ExpectedSymbol(format!("{value:?}"))),
                None => format!("{}-{}", spec_predicate_name(&spec[1]), guts.name),
            };
            let mut conclusion = match &spec[1] {
                WorldValue::Symbol(predicate) => WorldValue::list([
                    WorldValue::Symbol(predicate.clone()),
                    WorldValue::Symbol(return_name.clone()),
                ]),
                term => acl2_subst(
                    &WorldValue::Symbol(return_name.clone()),
                    &WorldValue::Symbol("x".into()),
                    term,
                ),
            };
            if let Some(hypothesis) = keywords.get(":hyp") {
                conclusion = WorldValue::list([
                    WorldValue::Symbol("implies".into()),
                    hypothesis.clone(),
                    conclusion,
                ]);
            }
            let formula = WorldValue::list([
                WorldValue::Symbol("b*".into()),
                WorldValue::list([WorldValue::list([pattern.clone(), call.clone()])]),
                conclusion,
            ]);
            let mut theorem = vec![
                WorldValue::Symbol("defthm".into()),
                WorldValue::Symbol(theorem_name),
                formula,
            ];
            for keyword in [":hints", ":rule-classes"] {
                if let Some(value) = keywords.get(keyword) {
                    theorem.push(WorldValue::Symbol(keyword.into()));
                    theorem.push(value.clone());
                }
            }
            events.push(WorldValue::list(theorem));
        }
        Ok(WorldValue::list(events))
    }

    /// Evaluate the data-oriented LOOP$ subset used by x86isa make-events.
    ///
    /// This deliberately supports only the eager, finite list traversal
    /// spelling `(loop$ for x in xs [when/unless p] collect/append body)`.
    /// It is read-time computation and does not admit a recursive definition
    /// or establish any theorem.
    fn eval_loop(
        &mut self,
        items: &[SExpr],
        locals: &BTreeMap<String, WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        if items.len() < 7 || symbol(&items[1]) != Some("for") || symbol(&items[3]) != Some("in") {
            return Err(WorldError::Malformed("loop$"));
        }
        let variable = symbol(&items[2]).ok_or(WorldError::Malformed("loop$ variable"))?;
        let input = proper_list(self.eval(&items[4], locals)?)?;
        let mut cursor = 5;
        let filter = match items.get(cursor).and_then(symbol) {
            Some("when" | "unless") => {
                let polarity = symbol(&items[cursor]) == Some("when");
                let predicate = items
                    .get(cursor + 1)
                    .ok_or(WorldError::Malformed("loop$ filter"))?;
                cursor += 2;
                Some((polarity, predicate))
            }
            _ => None,
        };
        let mode = items
            .get(cursor)
            .and_then(symbol)
            .ok_or(WorldError::Malformed("loop$ result clause"))?;
        if !matches!(mode, "collect" | "append") || cursor + 2 != items.len() {
            return Err(WorldError::Malformed("loop$ result clause"));
        }
        let body = &items[cursor + 1];
        let mut output = Vec::new();
        for value in input {
            let mut scope = locals.clone();
            scope.insert(variable.into(), value);
            if let Some((polarity, predicate)) = filter
                && self.eval(predicate, &scope)?.is_true() != polarity
            {
                continue;
            }
            let value = self.eval(body, &scope)?;
            if mode == "append" {
                output.extend(proper_list(value)?);
            } else {
                output.push(value);
            }
        }
        Ok(WorldValue::list(output.into_iter()))
    }

    fn quasiquote(
        &mut self,
        expr: &SExpr,
        locals: &BTreeMap<String, WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        if let Some(items) = list(expr) {
            if items.first().and_then(symbol) == Some("unquote") && items.len() == 2 {
                return self.eval(&items[1], locals);
            }
            let mut values = Vec::new();
            for item in items {
                if let Some(splice) = list(item)
                    && splice.first().and_then(symbol) == Some("unquote-splicing")
                    && splice.len() == 2
                {
                    values.extend(proper_list(self.eval(&splice[1], locals)?)?);
                } else {
                    values.push(self.quasiquote(item, locals)?);
                }
            }
            Ok(WorldValue::list(values.into_iter()))
        } else {
            quote(expr)
        }
    }

    fn apply(&mut self, head: &str, args: Vec<WorldValue>) -> Result<WorldValue, WorldError> {
        match head {
            "inst-list-prefix-byte-group-code" => iterative_inst_list_prefix_byte_group_code(args),
            "compute-modr/m-for-opcodes" => self.iterative_compute_modrm_for_opcodes(args),
            "any-inst-needs-modr/m-p" => self.iterative_any_inst_needs_modrm(args),
            "inst-needs-modr/m-p" => self.iterative_inst_needs_modrm(args),
            "operand-needs-modr/m-p" => self.iterative_operand_needs_modrm(args),
            "select-insts" => iterative_select_insts(args),
            "remove-insts-with-feat" => iterative_filter_insts_with_feat(args, false),
            "keep-insts-with-feat" => iterative_filter_insts_with_feat(args, true),
            "opcode-present?" => iterative_opcode_present(args),
            "+" => int_fold(args, Int::zero(), |a, b| a + b),
            "*" => int_fold(args, Int::one(), |a, b| a * b),
            "-" => {
                let ints = ints(args)?;
                match ints.as_slice() {
                    [value] => Ok(WorldValue::Int(-value)),
                    [first, rest @ ..] => Ok(WorldValue::Int(
                        rest.iter().fold(first.clone(), |value, item| value - item),
                    )),
                    [] => Err(WorldError::Arity("-")),
                }
            }
            "/" => {
                let ints = ints(args)?;
                match ints.as_slice() {
                    [first, rest @ ..] if !rest.is_empty() => Ok(WorldValue::Int(
                        rest.iter().fold(first.clone(), |value, item| value / item),
                    )),
                    _ => Err(WorldError::Arity("/")),
                }
            }
            "1+" => unary_int(args, |value| value + Int::one()),
            "1-" => unary_int(args, |value| value - Int::one()),
            "expt" => {
                let ints = ints(args)?;
                let [base, exponent] = ints.as_slice() else {
                    return Err(WorldError::Arity("expt"));
                };
                let exponent =
                    u32::try_from(i64::try_from(exponent).map_err(|_| WorldError::Range("expt"))?)
                        .map_err(|_| WorldError::Range("expt"))?;
                Ok(WorldValue::Int(base.clone().pow(exponent)))
            }
            "floor" => binary_int(args, |a, b| a / b),
            "mod" => binary_int(args, |a, b| {
                let remainder = &a % &b;
                if remainder.is_negative() {
                    remainder + b
                } else {
                    remainder
                }
            }),
            "max" => binary_int(args, |a, b| if a >= b { a } else { b }),
            "ash" => {
                let ints = ints(args)?;
                let [value, count] = ints.as_slice() else {
                    return Err(WorldError::Arity("ash"));
                };
                let count = i64::try_from(count).map_err(|_| WorldError::Range("ash"))?;
                let shifted = if count >= 0 {
                    value.as_inner() << usize::try_from(count).expect("nonnegative")
                } else {
                    value.as_inner()
                        >> usize::try_from(-count).map_err(|_| WorldError::Range("ash"))?
                };
                Ok(WorldValue::Int(Int::from_inner(shifted)))
            }
            "loghead" => {
                let ints = ints(args)?;
                let [width, value] = ints.as_slice() else {
                    return Err(WorldError::Arity("loghead"));
                };
                let width = usize_from_int(width, "loghead")?;
                let modulus = Int::from(2u64)
                    .pow(u32::try_from(width).map_err(|_| WorldError::Range("loghead"))?);
                let mut result = value % &modulus;
                if result.is_negative() {
                    result += &modulus;
                }
                Ok(WorldValue::Int(result))
            }
            "logtail" => {
                let ints = ints(args)?;
                let [width, value] = ints.as_slice() else {
                    return Err(WorldError::Arity("logtail"));
                };
                let shifted = value.as_inner() >> usize_from_int(width, "logtail")?;
                Ok(WorldValue::Int(Int::from_inner(shifted)))
            }
            "logand" | "logior" | "logxor" => {
                let ints = ints(args)?;
                let mut values = ints.into_iter();
                let first = values.next().ok_or(WorldError::Arity("bit operation"))?;
                let result = values.fold(first.into_inner(), |left, right| match head {
                    "logand" => left & right.into_inner(),
                    "logior" => left | right.into_inner(),
                    _ => left ^ right.into_inner(),
                });
                Ok(WorldValue::Int(Int::from_inner(result)))
            }
            "<" => compare_int(args, |a, b| a < b),
            "<=" => compare_int(args, |a, b| a <= b),
            ">" => compare_int(args, |a, b| a > b),
            ">=" => compare_int(args, |a, b| a >= b),
            "equal" | "eql" | "eq" => {
                let [left, right] = args.as_slice() else {
                    return Err(WorldError::Arity("equal"));
                };
                Ok(WorldValue::truth(left == right))
            }
            "mk-name" | "mksym" => {
                let mut name = String::new();
                for value in args {
                    match value {
                        WorldValue::Symbol(part) => name.push_str(
                            part.rsplit_once("::")
                                .map_or(part.as_str(), |(_, name)| name),
                        ),
                        WorldValue::String(part) => name.push_str(
                            std::str::from_utf8(&part)
                                .map_err(|_| WorldError::Malformed("mk-name string"))?,
                        ),
                        WorldValue::Int(part) => name.push_str(&part.to_string()),
                        _ => return Err(WorldError::Malformed("mk-name component")),
                    }
                }
                Ok(WorldValue::Symbol(name.to_ascii_lowercase()))
            }
            "concatenate" => {
                let [WorldValue::Symbol(result_type), pieces @ ..] = args.as_slice() else {
                    return Err(WorldError::Arity("concatenate"));
                };
                if result_type != "string" {
                    return Err(WorldError::UnsupportedOperation(format!(
                        "concatenate result type `{result_type}`"
                    )));
                }
                let mut output = Vec::new();
                for piece in pieces {
                    let WorldValue::String(piece) = piece else {
                        return Err(WorldError::Malformed("concatenate string argument"));
                    };
                    output.extend_from_slice(piece);
                }
                Ok(WorldValue::String(output))
            }
            "str::cat" => {
                let mut output = Vec::new();
                for piece in args {
                    let WorldValue::String(piece) = piece else {
                        return Err(WorldError::Malformed("str::cat argument"));
                    };
                    output.extend(piece);
                }
                Ok(WorldValue::String(output))
            }
            "str::implode" => {
                let [characters] = args.as_slice() else {
                    return Err(WorldError::Arity("str::implode"));
                };
                let characters = proper_list(characters.clone())?;
                let mut output = Vec::with_capacity(characters.len());
                for character in characters {
                    let WorldValue::Symbol(literal) = character else {
                        return Err(WorldError::Malformed("str::implode character"));
                    };
                    output.push(
                        acl2_character_byte(&literal)
                            .ok_or(WorldError::Malformed("str::implode character"))?,
                    );
                }
                Ok(WorldValue::String(output))
            }
            "str::nat-to-dec-string" | "str::natstr" => {
                let [WorldValue::Int(value)] = args.as_slice() else {
                    return Err(WorldError::Arity("str::nat-to-dec-string"));
                };
                if value.is_negative() {
                    return Err(WorldError::Range("str::nat-to-dec-string"));
                }
                Ok(WorldValue::String(value.to_string().into_bytes()))
            }
            "string" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("string"));
                };
                let WorldValue::Symbol(literal) = value else {
                    return Err(WorldError::Malformed("string character argument"));
                };
                Ok(WorldValue::String(vec![
                    acl2_character_byte(literal)
                        .ok_or(WorldError::Malformed("string character argument"))?,
                ]))
            }
            "acl2::packn" => {
                let [parts] = args.as_slice() else {
                    return Err(WorldError::Arity("acl2::packn"));
                };
                let mut name = String::new();
                for part in proper_list(parts.clone())? {
                    match part {
                        WorldValue::Symbol(part) => name.push_str(
                            part.rsplit_once("::")
                                .map_or(part.as_str(), |(_, name)| name)
                                .trim_start_matches(':'),
                        ),
                        WorldValue::String(part) => name.push_str(
                            std::str::from_utf8(&part)
                                .map_err(|_| WorldError::Malformed("acl2::packn string"))?,
                        ),
                        WorldValue::Int(part) => name.push_str(&part.to_string()),
                        WorldValue::Nil => name.push_str("nil"),
                        WorldValue::List(_) | WorldValue::Cons(_, _) => {
                            return Err(WorldError::Malformed("acl2::packn component"));
                        }
                    }
                }
                Ok(WorldValue::Symbol(name.to_ascii_lowercase()))
            }
            "acl2::subst" => {
                let [new, old, tree] = args.as_slice() else {
                    return Err(WorldError::Arity("acl2::subst"));
                };
                Ok(acl2_subst(new, old, tree))
            }
            "acl2::type-set-quote" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("acl2::type-set-quote"));
                };
                Ok(WorldValue::Int(Int::from(acl2_type_set_quote(value))))
            }
            "acl2::ts-union" => {
                if args.is_empty() {
                    return Err(WorldError::Arity("acl2::ts-union"));
                }
                let values = ints(args)?;
                let union = values.into_iter().fold(Int::zero(), |left, right| {
                    Int::from_inner(left.into_inner() | right.into_inner())
                });
                Ok(WorldValue::Int(union))
            }
            "acl2::ens" => {
                let [WorldValue::Symbol(state)] = args.as_slice() else {
                    return Err(WorldError::Arity("acl2::ens"));
                };
                if state != "state" {
                    return Err(WorldError::Malformed("acl2::ens state"));
                }
                Ok(WorldValue::Symbol("acl2-enabled-structure".into()))
            }
            "acl2::convert-type-set-to-term" => {
                let [
                    variable,
                    WorldValue::Int(type_set),
                    WorldValue::Symbol(enabled),
                    WorldValue::Symbol(world),
                    ttree,
                ] = args.as_slice()
                else {
                    return Err(WorldError::Arity("acl2::convert-type-set-to-term"));
                };
                if enabled != "acl2-enabled-structure" || world != "acl2-world" {
                    return Err(WorldError::Malformed(
                        "acl2::convert-type-set-to-term world",
                    ));
                }
                let type_set = i64::try_from(type_set)
                    .map_err(|_| WorldError::Range("acl2::convert-type-set-to-term"))?;
                let term = acl2_convert_enum_type_set(variable, type_set)?;
                Ok(WorldValue::list([term, ttree.clone()]))
            }
            "w" => {
                let [WorldValue::Symbol(state)] = args.as_slice() else {
                    return Err(WorldError::Arity("w"));
                };
                if state != "state" {
                    return Err(WorldError::Malformed("w state"));
                }
                Ok(WorldValue::Symbol("acl2-world".into()))
            }
            "default-defun-mode" => {
                let [WorldValue::Symbol(world)] = args.as_slice() else {
                    return Err(WorldError::Arity("default-defun-mode"));
                };
                if world != "acl2-world" {
                    return Err(WorldError::Malformed("default-defun-mode world"));
                }
                // The inventory world never processes mode-changing commands.
                // Its ordered logical default is therefore ACL2's :logic.
                Ok(WorldValue::Symbol(":logic".into()))
            }
            "supported-platform?" => {
                if !args.is_empty() {
                    return Err(WorldError::Arity("supported-platform?"));
                }
                // This mirrors the reader-conditionals in x86isa's definition:
                // Linux, Darwin, and FreeBSD have a syscall implementation.
                Ok(WorldValue::truth(cfg!(any(
                    target_os = "linux",
                    target_os = "macos",
                    target_os = "freebsd"
                ))))
            }
            "acl2::formals" => {
                let [WorldValue::Symbol(name), WorldValue::Symbol(world)] = args.as_slice() else {
                    return Err(WorldError::Arity("acl2::formals"));
                };
                if world != "acl2-world" {
                    return Err(WorldError::Malformed("acl2::formals world"));
                }
                let function = self
                    .functions
                    .get(name)
                    .ok_or_else(|| WorldError::UnknownFunction(name.clone()))?;
                Ok(WorldValue::list(
                    function
                        .required
                        .iter()
                        .cloned()
                        .chain(function.keys.iter().map(|key| key.parameter.name.clone()))
                        .map(WorldValue::Symbol),
                ))
            }
            "defret-fn" => {
                let [name, arguments, disable, WorldValue::Symbol(world)] = args.as_slice() else {
                    return Err(WorldError::Arity("defret-fn"));
                };
                if world != "acl2-world" {
                    return Err(WorldError::Malformed("defret-fn world"));
                }
                self.expand_defret(name, arguments, disable.is_true())
            }
            "more-returns-fn" => {
                let [arguments, WorldValue::Symbol(world)] = args.as_slice() else {
                    return Err(WorldError::Arity("more-returns-fn"));
                };
                if world != "acl2-world" {
                    return Err(WorldError::Malformed("more-returns-fn world"));
                }
                self.expand_more_returns(arguments)
            }
            "not" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("not"));
                };
                Ok(WorldValue::truth(!value.is_true()))
            }
            "null" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("null"));
                };
                Ok(WorldValue::truth(matches!(value, WorldValue::Nil)))
            }
            "true-listp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("true-listp"));
                };
                Ok(WorldValue::truth(proper_list(value.clone()).is_ok()))
            }
            "consp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("consp"));
                };
                Ok(WorldValue::truth(
                    matches!(
                        value,
                        WorldValue::List(values) if !values.is_empty()
                    ) || matches!(value, WorldValue::Cons(_, _)),
                ))
            }
            "atom" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("atom"));
                };
                Ok(WorldValue::truth(
                    !matches!(value, WorldValue::List(values) if !values.is_empty())
                        && !matches!(value, WorldValue::Cons(_, _)),
                ))
            }
            "stringp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("stringp"));
                };
                Ok(WorldValue::truth(matches!(value, WorldValue::String(_))))
            }
            "symbolp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("symbolp"));
                };
                Ok(WorldValue::truth(match value {
                    WorldValue::Nil => true,
                    WorldValue::Symbol(name) => !name.starts_with("#\\"),
                    _ => false,
                }))
            }
            "characterp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("characterp"));
                };
                Ok(WorldValue::truth(matches!(
                    value,
                    WorldValue::Symbol(name) if acl2_character_byte(name).is_some()
                )))
            }
            "eqlablep" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("eqlablep"));
                };
                // This world contains only ACL2 integers among numbers; ACL2
                // symbols, characters, and numbers are EQL-able, while
                // strings and conses are not.
                Ok(WorldValue::truth(matches!(
                    value,
                    WorldValue::Nil | WorldValue::Int(_) | WorldValue::Symbol(_)
                )))
            }
            "char-code" => {
                let [WorldValue::Symbol(value)] = args.as_slice() else {
                    return Err(WorldError::Arity("char-code"));
                };
                Ok(WorldValue::Int(Int::from(u64::from(
                    acl2_character_byte(value)
                        .ok_or(WorldError::Malformed("char-code argument"))?,
                ))))
            }
            "keywordp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("keywordp"));
                };
                Ok(WorldValue::truth(matches!(
                    value,
                    WorldValue::Symbol(name) if name.starts_with(':')
                )))
            }
            "nat-listp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("nat-listp"));
                };
                Ok(WorldValue::truth(proper_list(value.clone()).is_ok_and(
                    |items| {
                        items
                            .iter()
                            .all(|item| item.as_int().is_some_and(|value| !value.is_negative()))
                    },
                )))
            }
            "str::strpos" => {
                let [needle, haystack] = args.as_slice() else {
                    return Err(WorldError::Arity("str::strpos"));
                };
                let (WorldValue::String(needle), WorldValue::String(haystack)) = (needle, haystack)
                else {
                    return Ok(WorldValue::Nil);
                };
                Ok(haystack
                    .windows(needle.len())
                    .position(|window| window == needle)
                    .map_or(WorldValue::Nil, |index| WorldValue::Int(Int::from(index))))
            }
            "subseq" => {
                let [WorldValue::String(value), start, end] = args.as_slice() else {
                    return Err(WorldError::Arity("subseq"));
                };
                let start = start
                    .as_int()
                    .map(|value| usize_from_int(value, "subseq"))
                    .transpose()?
                    .unwrap_or(0);
                let end = end
                    .as_int()
                    .map(|value| usize_from_int(value, "subseq"))
                    .transpose()?
                    .unwrap_or(value.len());
                let slice = value.get(start..end).ok_or(WorldError::Range("subseq"))?;
                Ok(WorldValue::String(slice.to_vec()))
            }
            "str::strtok" => {
                let [WorldValue::String(value), _separators] = args.as_slice() else {
                    return Err(WorldError::Arity("str::strtok"));
                };
                Ok(WorldValue::list(
                    value
                        .split(|byte| *byte == b'.')
                        .map(|part| WorldValue::String(part.to_vec())),
                ))
            }
            "acl2::nat-list-fix" => {
                let [values] = args.as_slice() else {
                    return Err(WorldError::Arity("acl2::nat-list-fix"));
                };
                Ok(WorldValue::list(
                    proper_list(values.clone())?.into_iter().map(|value| {
                        let value = value.as_int().cloned().unwrap_or_else(Int::zero);
                        WorldValue::Int(if value.is_negative() {
                            Int::zero()
                        } else {
                            value
                        })
                    }),
                ))
            }
            "str::strval" => {
                let [WorldValue::String(value)] = args.as_slice() else {
                    return Err(WorldError::Arity("str::strval"));
                };
                let value = std::str::from_utf8(value)
                    .map_err(|_| WorldError::Malformed("str::strval"))?
                    .parse::<Int>()
                    .map_err(|_| WorldError::Malformed("str::strval"))?;
                Ok(WorldValue::Int(value))
            }
            "symbol-name" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("symbol-name"));
                };
                let WorldValue::Symbol(value) = value else {
                    return Err(WorldError::ExpectedSymbol(format!("{value:?}")));
                };
                Ok(WorldValue::String(acl2_symbol_name(value).into_bytes()))
            }
            "intern" | "intern$" => {
                let [WorldValue::String(name), WorldValue::String(package)] = args.as_slice()
                else {
                    return Err(WorldError::Arity("intern"));
                };
                let name =
                    std::str::from_utf8(name).map_err(|_| WorldError::Malformed("intern name"))?;
                let package = std::str::from_utf8(package)
                    .map_err(|_| WorldError::Malformed("intern package"))?;
                // The reader's canonical surface spelling represents keyword
                // symbols with a leading colon. Other packages retain their
                // explicit ACL2 package qualifier.
                let symbol = if package.eq_ignore_ascii_case("KEYWORD") {
                    format!(":{}", name.to_ascii_lowercase())
                } else if package.eq_ignore_ascii_case("ACL2") {
                    name.to_ascii_lowercase()
                } else {
                    format!(
                        "{}::{}",
                        package.to_ascii_lowercase(),
                        name.to_ascii_lowercase()
                    )
                };
                Ok(WorldValue::Symbol(symbol))
            }
            "intern-in-package-of-symbol" => {
                let [WorldValue::String(name), WorldValue::Symbol(prototype)] = args.as_slice()
                else {
                    return Err(WorldError::Arity("intern-in-package-of-symbol"));
                };
                let name = std::str::from_utf8(name)
                    .map_err(|_| WorldError::Malformed("intern-in-package-of-symbol name"))?
                    .to_ascii_lowercase();
                let package = prototype
                    .rsplit_once("::")
                    .map(|(package, _)| format!("{package}::"))
                    .unwrap_or_default();
                Ok(WorldValue::Symbol(format!("{package}{name}")))
            }
            "std::strip-p-from-symbol" => {
                let [WorldValue::Symbol(symbol)] = args.as_slice() else {
                    return Err(WorldError::Arity("std::strip-p-from-symbol"));
                };
                let (package, name) = symbol
                    .rsplit_once("::")
                    .map_or(("", symbol.as_str()), |(package, name)| (package, name));
                let stripped = name.strip_suffix("-p").unwrap_or(name);
                Ok(WorldValue::Symbol(if package.is_empty() {
                    stripped.into()
                } else {
                    format!("{package}::{stripped}")
                }))
            }
            "function-symbolp" => {
                let [WorldValue::Symbol(name), WorldValue::Symbol(world)] = args.as_slice() else {
                    return Err(WorldError::Arity("function-symbolp"));
                };
                if world != "acl2-world" {
                    return Err(WorldError::Malformed("function-symbolp world"));
                }
                Ok(WorldValue::truth(self.functions.contains_key(name)))
            }
            "value" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("value"));
                };
                Ok(WorldValue::list([
                    WorldValue::Nil,
                    value.clone(),
                    WorldValue::Symbol("state".into()),
                ]))
            }
            "member-symbol-name" => {
                let [WorldValue::String(name), names] = args.as_slice() else {
                    return Err(WorldError::Arity("member-symbol-name"));
                };
                Ok(WorldValue::truth(proper_list(names.clone()).is_ok_and(
                    |names| {
                        names.iter().any(|candidate| match candidate {
                            WorldValue::Symbol(candidate) => {
                                candidate.as_bytes().eq_ignore_ascii_case(name)
                            }
                            WorldValue::String(candidate) => candidate.eq_ignore_ascii_case(name),
                            _ => false,
                        })
                    },
                )))
            }
            "all-opcode-maps" => {
                if !args.is_empty() {
                    return Err(WorldError::Arity("all-opcode-maps"));
                }
                let mut maps = Vec::new();
                for name in pre_opcode_map_names() {
                    maps.extend(proper_list(
                        self.constants
                            .get(name)
                            .cloned()
                            .ok_or_else(|| WorldError::Unbound(name.into()))?,
                    )?);
                }
                Ok(WorldValue::list(maps.into_iter()))
            }
            "find-insts-named" => {
                let [names, insts] = args.as_slice() else {
                    return Err(WorldError::Arity("find-insts-named"));
                };
                let names = proper_list(names.clone())?;
                let mut found = Vec::new();
                for inst in proper_list(insts.clone())? {
                    let fields = proper_list(inst.clone())?;
                    let Some(mnemonic) = fields.get(1) else {
                        continue;
                    };
                    let matches = names.iter().any(|name| match (name, mnemonic) {
                        (WorldValue::Symbol(left), WorldValue::Symbol(right)) => {
                            left.eq_ignore_ascii_case(right)
                        }
                        (WorldValue::Symbol(left), WorldValue::String(right)) => {
                            left.as_bytes().eq_ignore_ascii_case(right)
                        }
                        (WorldValue::String(left), WorldValue::String(right)) => {
                            left.eq_ignore_ascii_case(right)
                        }
                        _ => false,
                    });
                    if matches {
                        found.push(inst);
                    }
                }
                Ok(WorldValue::list(found.into_iter()))
            }
            "symbol-list->names" => {
                let [symbols] = args.as_slice() else {
                    return Err(WorldError::Arity("symbol-list->names"));
                };
                let mut names = Vec::new();
                for symbol in proper_list(symbols.clone())? {
                    let WorldValue::Symbol(symbol) = symbol else {
                        names.push(symbol);
                        continue;
                    };
                    let mut recovered = None;
                    'maps: for map_name in pre_opcode_map_names() {
                        let Some(map) = self.constants.get(map_name) else {
                            continue;
                        };
                        for inst in proper_list(map.clone())? {
                            if let Some(WorldValue::String(mnemonic)) = proper_list(inst)?.get(1)
                                && symbol.as_bytes().eq_ignore_ascii_case(mnemonic)
                            {
                                recovered = Some(mnemonic.clone());
                                break 'maps;
                            }
                        }
                    }
                    names.push(WorldValue::String(
                        recovered.unwrap_or_else(|| acl2_symbol_name(&symbol).into_bytes()),
                    ));
                }
                Ok(WorldValue::list(names.into_iter()))
            }
            "inst-list->mnemonics" => {
                let [insts] = args.as_slice() else {
                    return Err(WorldError::Arity("inst-list->mnemonics"));
                };
                let mut names = Vec::new();
                for inst in proper_list(insts.clone())? {
                    if let Some(name) = proper_list(inst)?.get(1) {
                        names.push(name.clone());
                    }
                }
                Ok(WorldValue::list(names.into_iter()))
            }
            "keep-strings" => {
                let [values] = args.as_slice() else {
                    return Err(WorldError::Arity("keep-strings"));
                };
                Ok(WorldValue::list(
                    proper_list(values.clone())?
                        .into_iter()
                        .filter(|value| matches!(value, WorldValue::String(_))),
                ))
            }
            "inst-fix" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("inst-fix"));
                };
                Ok(value.clone())
            }
            "keep-implemented-insts" | "keep-unimplemented-insts" => {
                let [insts] = args.as_slice() else {
                    return Err(WorldError::Arity("keep instruction list"));
                };
                let keep_implemented = head == "keep-implemented-insts";
                let mut kept = Vec::new();
                for inst in proper_list(insts.clone())? {
                    let fields = proper_list(inst.clone())?;
                    let implemented = fields.get(4).is_some_and(WorldValue::is_true);
                    if implemented == keep_implemented {
                        kept.push(inst);
                    }
                }
                Ok(WorldValue::list(kept.into_iter()))
            }
            "eval-feature-expr" => {
                let [expr, inst] = args.as_slice() else {
                    return Err(WorldError::Arity("eval-feature-expr"));
                };
                Ok(WorldValue::truth(eval_feature_expr(expr, inst)?))
            }
            "keep-insts-satisfying-feature" => {
                let [expr, insts] = args.as_slice() else {
                    return Err(WorldError::Arity("keep-insts-satisfying-feature"));
                };
                let mut kept = Vec::new();
                for inst in proper_list(insts.clone())? {
                    if eval_feature_expr(expr, &inst)? {
                        kept.push(inst);
                    }
                }
                Ok(WorldValue::list(kept.into_iter()))
            }
            "inst->fn" | "inst->mnemonic" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("inst accessor"));
                };
                let fields = proper_list(value.clone())?;
                Ok(fields
                    .get(if head == "inst->mnemonic" { 1 } else { 4 })
                    .cloned()
                    .unwrap_or(WorldValue::Nil))
            }
            "set-difference-equal" => {
                let [left, right] = args.as_slice() else {
                    return Err(WorldError::Arity("set-difference-equal"));
                };
                let right = proper_list(right.clone())?;
                Ok(WorldValue::list(
                    proper_list(left.clone())?
                        .into_iter()
                        .filter(|value| !right.contains(value)),
                ))
            }
            "put-assoc" | "put-assoc-eq" | "put-assoc-eql" | "put-assoc-equal" => {
                let [key, value, alist] = args.as_slice() else {
                    return Err(WorldError::Arity("put-assoc"));
                };
                let mut entries = proper_list(alist.clone())?;
                let replacement = WorldValue::Cons(Box::new(key.clone()), Box::new(value.clone()));
                if let Some(entry) = entries.iter_mut().find(|entry| acl2_car(entry) == *key) {
                    *entry = replacement;
                } else {
                    entries.push(replacement);
                }
                Ok(WorldValue::list(entries))
            }
            "make-sdm-instruction-table-entry" => Ok(WorldValue::list(args.into_iter())),
            "sdm-instruction-table-xdoc-events" => {
                let [table, WorldValue::Symbol(_parent)] = args.as_slice() else {
                    return Err(WorldError::Arity("sdm-instruction-table-xdoc-events"));
                };
                // This generator's authored result is exclusively DEFxDOC and
                // XDOC::ORDER-SUBTOPICS events. Inventory evaluation does not
                // retain documentation bodies, so traversing the full x86
                // catalogue would add no logical surface and can exhaust the
                // native stack on its recursive hierarchy.
                proper_list(table.clone())?;
                Ok(WorldValue::Nil)
            }
            "sdm-instruction-table-sort" => {
                let [table] = args.as_slice() else {
                    return Err(WorldError::Arity("sdm-instruction-table-sort"));
                };
                let mut rows = proper_list(table.clone())?;
                rows.sort_by(|left, right| {
                    let left = table_row_key(left).unwrap_or_default();
                    let right = table_row_key(right).unwrap_or_default();
                    left.cmp(&right)
                });
                Ok(WorldValue::list(rows.into_iter()))
            }
            "sdm-instruction-table-organize" | "sdm-instruction-table-fix" => {
                let [table] = args.as_slice() else {
                    return Err(WorldError::Arity("sdm instruction table"));
                };
                let mut rows = proper_list(table.clone())?;
                rows.sort_by(|left, right| {
                    table_row_key(left)
                        .unwrap_or_default()
                        .cmp(&table_row_key(right).unwrap_or_default())
                });
                Ok(WorldValue::list(rows.into_iter()))
            }
            "sdm-instruction-table-implemented-instructions"
            | "sdm-instruction-table-unimplemented-instructions" => {
                let [table] = args.as_slice() else {
                    return Err(WorldError::Arity("sdm instruction table accessor"));
                };
                let key = if head.contains("unimplemented") {
                    ":unimplemented"
                } else {
                    ":implemented"
                };
                let mut output = Vec::new();
                for row in proper_list(table.clone())? {
                    if let Some(entry) = table_row_value(&row) {
                        output.extend(entry_instruction_field(&entry, key));
                    }
                }
                Ok(WorldValue::list(output.into_iter()))
            }
            "keep-string-mnemonic-insts" => {
                let [insts] = args.as_slice() else {
                    return Err(WorldError::Arity("keep-string-mnemonic-insts"));
                };
                let mut output = Vec::new();
                for inst in proper_list(insts.clone())? {
                    if proper_list(inst.clone())?
                        .get(1)
                        .is_some_and(|name| matches!(name, WorldValue::String(_)))
                    {
                        output.push(inst);
                    }
                }
                Ok(WorldValue::list(output.into_iter()))
            }
            "set::mergesort" => {
                let [values] = args.as_slice() else {
                    return Err(WorldError::Arity("set::mergesort"));
                };
                let mut output = Vec::new();
                for value in proper_list(values.clone())? {
                    if !output.contains(&value) {
                        output.push(value);
                    }
                }
                Ok(WorldValue::list(output.into_iter()))
            }
            "set::difference" => {
                let [left, right] = args.as_slice() else {
                    return Err(WorldError::Arity("set::difference"));
                };
                let right = proper_list(right.clone())?;
                Ok(WorldValue::list(
                    proper_list(left.clone())?
                        .into_iter()
                        .filter(|value| !right.contains(value)),
                ))
            }
            "get-promoted-avx512-insts" => {
                let [section, feature, table] = args.as_slice() else {
                    return Err(WorldError::Arity("get-promoted-avx512-insts"));
                };
                let section = int_list(section).unwrap_or_default();
                let rows = proper_list(table.clone())?;
                let mut avx512_existing = Vec::new();
                let mut prior_mnemonics = Vec::new();
                for row in &rows {
                    let key = table_row_key(row).unwrap_or_default();
                    if key == section {
                        continue;
                    }
                    let Some(entry) = table_row_value(row) else {
                        continue;
                    };
                    let instructions = entry_instructions(&entry);
                    if key.starts_with(&[5, 19]) {
                        avx512_existing.extend(instructions.clone());
                    }
                    if key.starts_with(&[5, 13])
                        || key.starts_with(&[5, 15])
                        || key.starts_with(&[5, 16])
                    {
                        for inst in instructions {
                            if let Some(name) = proper_list(inst)?.get(1).cloned() {
                                prior_mnemonics.push(name);
                            }
                        }
                    }
                }
                let mut promoted = Vec::new();
                for name in pre_opcode_map_names() {
                    for inst in proper_list(
                        self.constants
                            .get(name)
                            .cloned()
                            .ok_or_else(|| WorldError::Unbound(name.into()))?,
                    )? {
                        if eval_feature_expr(feature, &inst)?
                            && !avx512_existing.contains(&inst)
                            && proper_list(inst.clone())?
                                .get(1)
                                .is_some_and(|mnemonic| prior_mnemonics.contains(mnemonic))
                        {
                            promoted.push(inst);
                        }
                    }
                }
                Ok(WorldValue::list(promoted.into_iter()))
            }
            "raise" => Err(WorldError::Raised(format!("{args:?}"))),
            "mbt" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("mbt"));
                };
                Ok(value.clone())
            }
            "natp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("natp"));
                };
                Ok(WorldValue::truth(
                    value.as_int().is_some_and(|value| !value.is_negative()),
                ))
            }
            "24bits-p" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("24bits-p"));
                };
                let limit = Int::from(2u64).pow(24);
                Ok(WorldValue::truth(value.as_int().is_some_and(|value| {
                    !value.is_negative() && value < &limit
                })))
            }
            "zp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("zp"));
                };
                Ok(WorldValue::truth(
                    value.as_int().is_none_or(|value| !value.is_positive()),
                ))
            }
            "cons" => {
                let [head, tail] = args.as_slice() else {
                    return Err(WorldError::Arity("cons"));
                };
                Ok(match tail {
                    WorldValue::Nil => WorldValue::List(vec![head.clone()]),
                    WorldValue::List(values) => {
                        let mut output = Vec::with_capacity(values.len() + 1);
                        output.push(head.clone());
                        output.extend(values.iter().cloned());
                        WorldValue::List(output)
                    }
                    _ => WorldValue::Cons(Box::new(head.clone()), Box::new(tail.clone())),
                })
            }
            "acons" => {
                let [key, value, alist] = args.as_slice() else {
                    return Err(WorldError::Arity("acons"));
                };
                let mut entries = Vec::new();
                entries.push(WorldValue::Cons(
                    Box::new(key.clone()),
                    Box::new(value.clone()),
                ));
                entries.extend(proper_list(alist.clone())?);
                Ok(WorldValue::list(entries))
            }
            "pairlis$" => {
                let [keys, values] = args.as_slice() else {
                    return Err(WorldError::Arity("pairlis$"));
                };
                // ACL2's PAIRLIS$ is total: it stops when KEYS is atomic and
                // uses (CAR VALUES), hence NIL, after VALUES is exhausted.
                // Build the proper alist iteratively so sizeable generated
                // memories do not consume the Rust call stack.
                let mut keys = keys.clone();
                let mut values = values.clone();
                let mut output = Vec::new();
                while matches!(
                    keys,
                    WorldValue::List(ref items) if !items.is_empty()
                ) || matches!(keys, WorldValue::Cons(_, _))
                {
                    output.push(WorldValue::Cons(
                        Box::new(acl2_car(&keys)),
                        Box::new(acl2_car(&values)),
                    ));
                    keys = acl2_cdr(&keys);
                    values = acl2_cdr(&values);
                }
                Ok(WorldValue::list(output))
            }
            "list" | "mv" => Ok(WorldValue::list(args.into_iter())),
            "append" => {
                let mut output = Vec::new();
                for value in args {
                    output.extend(proper_list(value)?);
                }
                Ok(WorldValue::list(output.into_iter()))
            }
            "strip-cars" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("strip-cars"));
                };
                Ok(WorldValue::list(
                    proper_list(value.clone())?
                        .into_iter()
                        .map(|entry| match entry {
                            WorldValue::Cons(head, _) => *head,
                            WorldValue::List(values) => {
                                values.into_iter().next().unwrap_or(WorldValue::Nil)
                            }
                            _ => WorldValue::Nil,
                        }),
                ))
            }
            "len" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("len"));
                };
                Ok(WorldValue::Int(Int::from(
                    proper_list(value.clone())?.len(),
                )))
            }
            "car" | "first" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("car"));
                };
                Ok(match value {
                    WorldValue::Cons(head, _) => (**head).clone(),
                    WorldValue::List(values) => values.first().cloned().unwrap_or(WorldValue::Nil),
                    _ => WorldValue::Nil,
                })
            }
            "cadr" | "second" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("cadr"));
                };
                Ok(match value {
                    WorldValue::Cons(_, tail) => match tail.as_ref() {
                        WorldValue::Cons(head, _) => (**head).clone(),
                        WorldValue::List(values) => {
                            values.first().cloned().unwrap_or(WorldValue::Nil)
                        }
                        _ => WorldValue::Nil,
                    },
                    WorldValue::List(values) => values.get(1).cloned().unwrap_or(WorldValue::Nil),
                    _ => WorldValue::Nil,
                })
            }
            "caar" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("caar"));
                };
                Ok(acl2_car(&acl2_car(value)))
            }
            "caaddr" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("caaddr"));
                };
                Ok(acl2_car(&acl2_car(&acl2_cdr(&acl2_cdr(value)))))
            }
            "cdr" | "rest" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("cdr"));
                };
                Ok(match value {
                    WorldValue::Cons(_, tail) => (**tail).clone(),
                    WorldValue::List(values) => WorldValue::list(values.iter().skip(1).cloned()),
                    _ => WorldValue::Nil,
                })
            }
            "cddr" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("cddr"));
                };
                Ok(acl2_cdr(&acl2_cdr(value)))
            }
            "last" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("last"));
                };
                Ok(acl2_last(value))
            }
            "member" | "member-equal" => {
                let [needle, haystack] = args.as_slice() else {
                    return Err(WorldError::Arity("member"));
                };
                let mut cursor = haystack;
                loop {
                    match cursor {
                        WorldValue::List(values) => {
                            let found = values.iter().position(|item| {
                                if head == "member-equal" {
                                    item == needle
                                } else {
                                    acl2_eql(item, needle)
                                }
                            });
                            return Ok(found.map_or(WorldValue::Nil, |index| {
                                WorldValue::list(values[index..].iter().cloned())
                            }));
                        }
                        WorldValue::Cons(item, tail) => {
                            let matches = if head == "member-equal" {
                                item.as_ref() == needle
                            } else {
                                acl2_eql(item, needle)
                            };
                            if matches {
                                return Ok(cursor.clone());
                            }
                            cursor = tail;
                        }
                        _ => return Ok(WorldValue::Nil),
                    }
                }
            }
            "assoc" | "assoc-equal" => {
                let [key, alist] = args.as_slice() else {
                    return Err(WorldError::Arity("assoc"));
                };
                for entry in proper_list(alist.clone())? {
                    let entry_key = match &entry {
                        WorldValue::Cons(entry_key, _) => Some(entry_key.as_ref()),
                        WorldValue::List(values) => values.first(),
                        _ => None,
                    };
                    let matches = entry_key.is_some_and(|entry_key| {
                        if head == "assoc-equal" {
                            entry_key == key
                        } else {
                            acl2_eql(entry_key, key)
                        }
                    });
                    if matches {
                        return Ok(entry);
                    }
                }
                Ok(WorldValue::Nil)
            }
            "assoc-keyword" => {
                let [key, plist] = args.as_slice() else {
                    return Err(WorldError::Arity("assoc-keyword"));
                };
                let values = proper_list(plist.clone())?;
                Ok(values
                    .iter()
                    .step_by(2)
                    .position(|candidate| candidate == key)
                    .map_or(WorldValue::Nil, |pair_index| {
                        WorldValue::list(values[pair_index * 2..].iter().cloned())
                    }))
            }
            "remove" => {
                let [value, list] = args.as_slice() else {
                    return Err(WorldError::Arity("remove"));
                };
                Ok(WorldValue::list(
                    proper_list(list.clone())?
                        .into_iter()
                        .filter(|item| !acl2_eql(item, value)),
                ))
            }
            "remove-equal" => {
                let [value, list] = args.as_slice() else {
                    return Err(WorldError::Arity("remove-equal"));
                };
                Ok(WorldValue::list(
                    proper_list(list.clone())?
                        .into_iter()
                        .filter(|item| item != value),
                ))
            }
            "no-duplicatesp-equal" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("no-duplicatesp-equal"));
                };
                // This is the executable ACL2 definition, evaluated without
                // recursion.  Dotted terminal tails are atoms and therefore
                // end the scan, just as ACL2's definition does.
                let mut cursor = value.clone();
                let mut seen = Vec::new();
                while matches!(
                    cursor,
                    WorldValue::List(ref items) if !items.is_empty()
                ) || matches!(cursor, WorldValue::Cons(_, _))
                {
                    let item = acl2_car(&cursor);
                    if seen.iter().any(|previous| previous == &item) {
                        return Ok(WorldValue::Nil);
                    }
                    seen.push(item);
                    cursor = acl2_cdr(&cursor);
                }
                Ok(WorldValue::Symbol("t".into()))
            }
            "endp" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("endp"));
                };
                Ok(WorldValue::truth(matches!(value, WorldValue::Nil)))
            }
            "increasing-list" => {
                let ints = ints(args)?;
                let [start, by, count] = ints.as_slice() else {
                    return Err(WorldError::Arity("increasing-list"));
                };
                let count = usize::try_from(
                    i64::try_from(count).map_err(|_| WorldError::Range("increasing-list"))?,
                )
                .map_err(|_| WorldError::Range("increasing-list"))?;
                let mut value = start.clone();
                let mut output = Vec::with_capacity(count);
                for _ in 0..count {
                    output.push(WorldValue::Int(value.clone()));
                    value += by;
                }
                Ok(WorldValue::list(output.into_iter()))
            }
            "max-list" => {
                let [value] = args.as_slice() else {
                    return Err(WorldError::Arity("max-list"));
                };
                let values = ints(proper_list(value.clone())?)?;
                values
                    .into_iter()
                    .max()
                    .map(WorldValue::Int)
                    .ok_or(WorldError::Range("max-list"))
            }
            _ => {
                let function = self
                    .functions
                    .get(head)
                    .cloned()
                    .ok_or_else(|| WorldError::UnknownFunction(head.into()))?;
                if args.len() < function.required.len() {
                    return Err(WorldError::Arity("defun call"));
                }
                let mut scope = function
                    .required
                    .iter()
                    .cloned()
                    .zip(args.iter().take(function.required.len()).cloned())
                    .collect::<BTreeMap<_, _>>();
                let trailing = &args[function.required.len()..];
                if function.keys.is_empty() {
                    if !trailing.is_empty() {
                        return Err(WorldError::Arity("defun call"));
                    }
                } else {
                    if trailing.len() % 2 != 0 {
                        return Err(WorldError::Arity("keyword defun call"));
                    }
                    let mut supplied = BTreeMap::new();
                    for pair in trailing.chunks_exact(2) {
                        let WorldValue::Symbol(keyword) = &pair[0] else {
                            return Err(WorldError::UnknownMacroKeyword(
                                head.into(),
                                format!("{:?}", pair[0]),
                            ));
                        };
                        let keyword = keyword.trim_start_matches(':');
                        if supplied
                            .insert(keyword.to_string(), pair[1].clone())
                            .is_some()
                        {
                            return Err(WorldError::DuplicateMacroKeyword(keyword.into()));
                        }
                    }
                    for key in function.keys {
                        let present = supplied.contains_key(&key.keyword);
                        let value = if let Some(value) = supplied.remove(&key.keyword) {
                            value
                        } else if let Some(default) = key.parameter.default {
                            self.eval(&default, &scope)?
                        } else {
                            WorldValue::Nil
                        };
                        scope.insert(key.parameter.name, value);
                        if let Some(supplied_name) = key.parameter.supplied {
                            scope.insert(supplied_name, WorldValue::truth(present));
                        }
                    }
                    if let Some(unknown) = supplied.keys().next() {
                        return Err(WorldError::UnknownMacroKeyword(
                            head.into(),
                            unknown.clone(),
                        ));
                    }
                }
                self.eval(&function.body, &scope)
            }
        }
    }

    /// Iterative execution counterpart of x86isa's recursive
    /// `compute-modr/m-for-opcodes`.
    ///
    /// The authored definition recurses once per opcode and, inside each
    /// step, once per matching instruction.  Keeping both walks flat is
    /// important because the generated tables are evaluated by a deliberately
    /// small-stack worker.
    fn iterative_compute_modrm_for_opcodes(
        &self,
        args: Vec<WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        let [WorldValue::Int(first), WorldValue::Int(count), insts] = args.as_slice() else {
            return Err(WorldError::Arity("compute-modr/m-for-opcodes"));
        };
        let count = usize_from_int(count, "compute-modr/m-for-opcodes")?;
        let insts = proper_list(insts.clone())?;
        let mut opcode = first.clone();
        let mut result = Vec::with_capacity(count);
        for _ in 0..count {
            if !self.is_24bits(&opcode) {
                return Err(WorldError::Range("compute-modr/m-for-opcodes"));
            }
            let mut needs_modrm = false;
            for inst in insts
                .iter()
                .filter(|inst| inst_opcode(inst) == Some(&opcode))
            {
                if self.inst_needs_modrm(inst)? {
                    needs_modrm = true;
                    break;
                }
            }
            result.push(WorldValue::Int(Int::from(i64::from(needs_modrm))));
            opcode += Int::one();
        }
        Ok(WorldValue::list(result))
    }

    fn iterative_any_inst_needs_modrm(
        &self,
        args: Vec<WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        let [insts] = args.as_slice() else {
            return Err(WorldError::Arity("any-inst-needs-modr/m-p"));
        };
        for inst in proper_list(insts.clone())? {
            if self.inst_needs_modrm(&inst)? {
                return Ok(WorldValue::Symbol("t".into()));
            }
        }
        Ok(WorldValue::Nil)
    }

    fn iterative_inst_needs_modrm(&self, args: Vec<WorldValue>) -> Result<WorldValue, WorldError> {
        let [inst] = args.as_slice() else {
            return Err(WorldError::Arity("inst-needs-modr/m-p"));
        };
        Ok(WorldValue::truth(self.inst_needs_modrm(inst)?))
    }

    fn iterative_operand_needs_modrm(
        &self,
        args: Vec<WorldValue>,
    ) -> Result<WorldValue, WorldError> {
        let [operand] = args.as_slice() else {
            return Err(WorldError::Arity("operand-needs-modr/m-p"));
        };
        Ok(WorldValue::truth(self.operand_needs_modrm(operand)?))
    }

    fn inst_needs_modrm(&self, inst: &WorldValue) -> Result<bool, WorldError> {
        let fields = proper_list(inst.clone())?;
        if fields.first() != Some(&WorldValue::Symbol("inst".into())) || fields.len() != 6 {
            return Err(WorldError::Malformed("inst-needs-modr/m-p instruction"));
        }
        let opcode = proper_list(fields[2].clone())?;
        if keyword_field(&opcode, ":superscripts")
            .and_then(|value| proper_list(value).ok())
            .is_some_and(|superscripts| {
                [":1a", ":1c"]
                    .iter()
                    .any(|name| superscripts.contains(&WorldValue::Symbol((*name).into())))
            })
        {
            return Ok(true);
        }
        let operands = unquote_world(&fields[3]);
        if !operands.is_true() {
            return Ok(false);
        }
        for operand in operands_fields(&operands)? {
            if self.operand_needs_modrm(&operand)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn operand_needs_modrm(&self, operand: &WorldValue) -> Result<bool, WorldError> {
        if !operand.is_true() {
            return Ok(false);
        }
        let operand = proper_list(unquote_world(operand))?;
        let Some(method) = operand.first() else {
            return Ok(false);
        };
        let info = self
            .constants
            .get("*z-addressing-method-info*")
            .ok_or_else(|| WorldError::Unbound("*z-addressing-method-info*".into()))?;
        for entry in proper_list(info.clone())? {
            let fields = proper_list(entry)?;
            if fields.first() != Some(method) {
                continue;
            }
            for property in &fields[1..] {
                match property {
                    WorldValue::Cons(key, value)
                        if key.as_ref() == &WorldValue::Symbol(":modr/m?".into()) =>
                    {
                        return Ok(value.is_true());
                    }
                    WorldValue::List(pair)
                        if pair.first() == Some(&WorldValue::Symbol(":modr/m?".into())) =>
                    {
                        // Dotted pairs are preserved by the reader as
                        // `(:key . value)` surface lists.  They can occur in
                        // constants installed before this evaluator has to
                        // inspect them.
                        return Ok(if pair.get(1) == Some(&WorldValue::Symbol(".".into())) {
                            pair.get(2).is_some_and(WorldValue::is_true)
                        } else {
                            pair.get(1).is_some_and(WorldValue::is_true)
                        });
                    }
                    _ => {}
                }
            }
            return Ok(false);
        }
        Ok(false)
    }

    fn is_24bits(&self, value: &Int) -> bool {
        !value.is_negative() && value < &Int::from(2u64).pow(24)
    }
}

impl Acl2WorldView for Acl2World {
    type Value = WorldValue;

    fn constant(&self, name: &str) -> Option<&Self::Value> {
        Acl2World::constant(self, name)
    }
}

impl Acl2EventWorld for Acl2World {
    type Form = SExpr;
    type Error = WorldError;

    fn process_world_event(&mut self, event: &Self::Form) -> Result<WorldEventStatus, Self::Error> {
        self.process_event(event).map(|handled| {
            if handled {
                WorldEventStatus::Handled
            } else {
                WorldEventStatus::Unhandled
            }
        })
    }
}

fn list(expr: &SExpr) -> Option<&[SExpr]> {
    match expr {
        SExpr::List(items) => Some(items),
        _ => None,
    }
}

fn symbol(expr: &SExpr) -> Option<&str> {
    match expr {
        SExpr::Atom(Atom::Symbol(value)) => Some(value),
        _ => None,
    }
}

fn bind_bstar_inst(
    scope: &mut BTreeMap<String, WorldValue>,
    name: &str,
    value: WorldValue,
) -> Result<(), WorldError> {
    let fields = proper_list(value.clone())?;
    if fields.first() != Some(&WorldValue::Symbol("inst".into())) || fields.len() != 6 {
        return Err(WorldError::Malformed("b* inst value"));
    }
    for (field, value) in ["mnemonic", "opcode", "operands", "fn", "excep"]
        .into_iter()
        .zip(fields[1..].iter())
    {
        scope.insert(format!("{name}.{field}"), value.clone());
    }
    scope.insert(name.into(), value);
    Ok(())
}

fn bind_bstar_opcode(
    scope: &mut BTreeMap<String, WorldValue>,
    name: &str,
    value: WorldValue,
) -> Result<(), WorldError> {
    let fields = proper_list(value.clone())?;
    if !matches!(
        fields.first(),
        Some(WorldValue::Symbol(tag)) if tag == "op" || tag == "opcode"
    ) || (fields.len() - 1) % 2 != 0
    {
        return Err(WorldError::Malformed("b* opcode value"));
    }
    for field in [
        "mode",
        "reg",
        "mod",
        "r/m",
        "pfx",
        "rex",
        "vex",
        "evex",
        "feat",
        "superscripts",
        "group",
    ] {
        scope.insert(format!("{name}.{field}"), WorldValue::Nil);
    }
    scope.insert(format!("{name}.op"), WorldValue::Int(Int::from(0)));
    for pair in fields[1..].chunks_exact(2) {
        let WorldValue::Symbol(keyword) = &pair[0] else {
            return Err(WorldError::Malformed("b* opcode field"));
        };
        let Some(field) = keyword.strip_prefix(':') else {
            return Err(WorldError::Malformed("b* opcode field"));
        };
        scope.insert(format!("{name}.{field}"), pair[1].clone());
    }
    scope.insert(name.into(), value);
    Ok(())
}

fn bind_bstar_operands(
    scope: &mut BTreeMap<String, WorldValue>,
    name: &str,
    value: WorldValue,
) -> Result<(), WorldError> {
    let fields = proper_list(value.clone())?;
    if !matches!(
        fields.first(),
        Some(WorldValue::Symbol(tag))
            if tag == "arg" || tag == "operands" || tag == "make-operands"
    ) {
        return Err(WorldError::Malformed("b* operands value"));
    }
    let operands = operands_fields_from_parts(&fields)?;
    for (field, value) in ["op1", "op2", "op3", "op4"].into_iter().zip(operands) {
        scope.insert(format!("{name}.{field}"), value);
    }
    scope.insert(name.into(), value);
    Ok(())
}

fn operands_fields(value: &WorldValue) -> Result<[WorldValue; 4], WorldError> {
    let fields = proper_list(value.clone())?;
    if !matches!(
        fields.first(),
        Some(WorldValue::Symbol(tag))
            if tag == "arg" || tag == "operands" || tag == "make-operands"
    ) {
        return Err(WorldError::Malformed("operands value"));
    }
    operands_fields_from_parts(&fields)
}

fn operands_fields_from_parts(fields: &[WorldValue]) -> Result<[WorldValue; 4], WorldError> {
    let mut result = std::array::from_fn(|_| WorldValue::Nil);
    if fields
        .get(1)
        .is_some_and(|field| matches!(field, WorldValue::Symbol(name) if name.starts_with(':')))
    {
        if (fields.len() - 1) % 2 != 0 {
            return Err(WorldError::Malformed("keyword operands value"));
        }
        for pair in fields[1..].chunks_exact(2) {
            let WorldValue::Symbol(keyword) = &pair[0] else {
                return Err(WorldError::Malformed("keyword operands field"));
            };
            let index = match keyword.as_str() {
                ":op1" => 0,
                ":op2" => 1,
                ":op3" => 2,
                ":op4" => 3,
                _ => return Err(WorldError::Malformed("keyword operands field")),
            };
            result[index] = unquote_world(&pair[1]);
        }
    } else {
        if fields.len() > 5 {
            return Err(WorldError::Malformed("positional operands value"));
        }
        for (target, value) in result.iter_mut().zip(&fields[1..]) {
            *target = unquote_world(value);
        }
    }
    Ok(result)
}

fn bind_bstar_cons_pattern(
    scope: &mut BTreeMap<String, WorldValue>,
    head_pattern: &SExpr,
    tail_pattern: &SExpr,
    value: WorldValue,
) -> Result<(), WorldError> {
    let head = acl2_car(&value);
    let tail = acl2_cdr(&value);
    bind_bstar_value_pattern(scope, head_pattern, head)?;
    bind_bstar_value_pattern(scope, tail_pattern, tail)
}

fn bind_bstar_value_pattern(
    scope: &mut BTreeMap<String, WorldValue>,
    pattern: &SExpr,
    value: WorldValue,
) -> Result<(), WorldError> {
    if let Some(name) = symbol(pattern) {
        let name = name.strip_prefix('?').unwrap_or(name);
        if name != "-" && name != "&" {
            scope.insert(name.into(), value);
        }
        return Ok(());
    }
    let pattern = list(pattern).ok_or_else(|| {
        WorldError::UnsupportedMacro(format!("unsupported b* value pattern `{pattern:?}`"))
    })?;
    match pattern.first().and_then(symbol) {
        Some("cons") if pattern.len() == 3 => {
            bind_bstar_cons_pattern(scope, &pattern[1], &pattern[2], value)
        }
        Some("sdm-instruction-table-entry") if pattern.len() == 2 => {
            let name = symbol(&pattern[1])
                .ok_or(WorldError::Malformed("b* instruction-table-entry name"))?;
            bind_sdm_instruction_table_entry(scope, name, value)
        }
        _ => Err(WorldError::UnsupportedMacro(format!(
            "unsupported b* value pattern `{pattern:?}`"
        ))),
    }
}

fn bind_sdm_instruction_table_entry(
    scope: &mut BTreeMap<String, WorldValue>,
    name: &str,
    value: WorldValue,
) -> Result<(), WorldError> {
    let fields = proper_list(value.clone())?;
    scope.insert(name.into(), value);
    for field in ["title", "implemented", "unimplemented", "doc", "subsecs"] {
        let keyword = WorldValue::Symbol(format!(":{field}"));
        let value = fields
            .windows(2)
            .find(|pair| pair[0] == keyword)
            .map(|pair| pair[1].clone())
            .unwrap_or(WorldValue::Nil);
        scope.insert(format!("{name}.{field}"), value);
    }
    Ok(())
}

fn is_declare(expr: &SExpr) -> bool {
    list(expr).and_then(|items| items.first()).and_then(symbol) == Some("declare")
}

fn is_macro_template_body(expr: &SExpr) -> bool {
    if matches!(
        expr,
        SExpr::Atom(Atom::Symbol(value)) if value == "t" || value == "nil" || value.starts_with(':')
    ) || matches!(expr, SExpr::Atom(Atom::Str { .. }))
    {
        return true;
    }
    let Some(items) = list(expr) else {
        return false;
    };
    match items.first().and_then(symbol) {
        Some("quote") => items.len() == 2,
        Some("quasiquote") => items.len() == 2,
        Some("if") if items.len() == 4 => {
            is_macro_template_body(&items[2])
                && matches!(
                    &items[3],
                    SExpr::Atom(Atom::Symbol(value)) if value == "nil"
                )
        }
        _ => false,
    }
}

fn macro_lambda_list(
    lambda: &[SExpr],
) -> Result<
    (
        Vec<String>,
        Vec<MacroParameter>,
        Option<String>,
        Vec<MacroKeyword>,
    ),
    WorldError,
> {
    #[derive(Clone, Copy, PartialEq)]
    enum Section {
        Required,
        Optional,
        Key,
    }

    let mut required = Vec::new();
    let mut optional = Vec::new();
    let mut rest = None;
    let mut keys = Vec::new();
    let mut index = 0;
    let mut section = Section::Required;
    while index < lambda.len() {
        let formal = symbol(&lambda[index]);
        if formal == Some("&optional") {
            if section != Section::Required {
                return Err(WorldError::UnsupportedMacro(
                    "&optional must precede &key".into(),
                ));
            }
            section = Section::Optional;
            index += 1;
            continue;
        }
        if formal == Some("&key") {
            if section == Section::Key || rest.is_some() {
                return Err(WorldError::UnsupportedMacro(
                    "&key may occur once and is not combined with &rest".into(),
                ));
            }
            section = Section::Key;
            index += 1;
            continue;
        }
        if formal == Some("&rest") {
            if section == Section::Key || rest.is_some() || index + 2 != lambda.len() {
                return Err(WorldError::UnsupportedMacro(
                    "&rest must be followed by the final plain symbol".into(),
                ));
            }
            rest = Some(
                symbol(&lambda[index + 1])
                    .ok_or(WorldError::Malformed("defmacro &rest formal"))?
                    .into(),
            );
            index += 2;
            continue;
        }
        if formal.is_some_and(|formal| formal.starts_with('&')) {
            return Err(WorldError::UnsupportedMacro(format!(
                "lambda-list keyword `{}` is not supported",
                formal.expect("checked")
            )));
        }
        match section {
            Section::Required => required.push(macro_formal_name(&lambda[index])?),
            Section::Optional => {
                optional.push(macro_parameter(&lambda[index], "defmacro &optional")?)
            }
            Section::Key => keys.push(macro_keyword(&lambda[index])?),
        }
        index += 1;
    }
    Ok((required, optional, rest, keys))
}

fn macro_keyword(expr: &SExpr) -> Result<MacroKeyword, WorldError> {
    let mut parameter = macro_parameter(expr, "defmacro &key")?;
    let mut keyword = parameter.name.clone();
    if let Some(spec) = list(expr)
        && let Some(designator) = spec.first().and_then(list)
        && designator
            .first()
            .and_then(symbol)
            .is_some_and(|name| name.starts_with(':'))
    {
        if designator.len() != 2 {
            return Err(WorldError::Malformed("defmacro destructured &key"));
        }
        keyword = symbol(&designator[0])
            .expect("checked")
            .trim_start_matches(':')
            .into();
        parameter.name = macro_formal_name(&designator[1])?;
    }
    Ok(MacroKeyword { keyword, parameter })
}

fn macro_parameter(expr: &SExpr, context: &'static str) -> Result<MacroParameter, WorldError> {
    match expr {
        SExpr::Atom(Atom::Symbol(name)) => Ok(MacroParameter {
            name: name.to_string(),
            default: None,
            supplied: None,
        }),
        SExpr::List(spec) if (1..=3).contains(&spec.len()) => Ok(MacroParameter {
            name: macro_formal_name(&spec[0])?,
            default: spec.get(1).cloned(),
            supplied: spec
                .get(2)
                .map(|form| {
                    symbol(form)
                        .map(str::to_owned)
                        .ok_or(WorldError::Malformed(context))
                })
                .transpose()?,
        }),
        _ => Err(WorldError::Malformed(context)),
    }
}

/// ACL2 permits guard-bearing formals such as `((x predicate) default)`.
/// The guard is admission metadata; macro expansion binds the leading name.
fn macro_formal_name(expr: &SExpr) -> Result<String, WorldError> {
    if let Some(name) = symbol(expr) {
        return Ok(name.into());
    }
    let guarded = list(expr).ok_or(WorldError::Malformed("defmacro formal"))?;
    let name = guarded
        .first()
        .and_then(symbol)
        .ok_or(WorldError::Malformed("defmacro guarded formal"))?;
    Ok(name.into())
}

fn is_keyword(expr: &SExpr) -> bool {
    symbol(expr).is_some_and(|symbol| symbol.starts_with(':'))
}

fn quote(expr: &SExpr) -> Result<WorldValue, WorldError> {
    match expr {
        SExpr::Atom(Atom::Symbol(value)) if value == "nil" => Ok(WorldValue::Nil),
        SExpr::Atom(Atom::Symbol(value)) => value
            .parse::<Int>()
            .map(WorldValue::Int)
            .or_else(|_| Ok(WorldValue::Symbol(value.to_string()))),
        SExpr::Atom(Atom::Str { bytes, .. }) => Ok(WorldValue::String(bytes.to_vec())),
        SExpr::List(items) => Ok(WorldValue::list(
            items
                .iter()
                .map(quote)
                .collect::<Result<Vec<_>, _>>()?
                .into_iter(),
        )),
    }
}

fn eval_feature_expr(expr: &WorldValue, inst: &WorldValue) -> Result<bool, WorldError> {
    let inst_fields = proper_list(inst.clone())?;
    let mnemonic = inst_fields.get(1).cloned().unwrap_or(WorldValue::Nil);
    let opcode = inst_fields.get(2).cloned().unwrap_or(WorldValue::Nil);
    let opcode_fields = proper_list(opcode)?;
    let field = |keyword: &str| {
        opcode_fields
            .windows(2)
            .find(|pair| pair[0] == WorldValue::Symbol(keyword.into()))
            .map(|pair| unquote_world(&pair[1]))
            .unwrap_or(WorldValue::Nil)
    };
    let member = |needle: &WorldValue, value: WorldValue| {
        proper_list(value)
            .map(|items| items.iter().any(|item| item == needle))
            .unwrap_or(false)
    };

    match expr {
        WorldValue::Nil => Ok(false),
        WorldValue::Symbol(symbol) => {
            let special = match symbol.as_str() {
                "t" => Some(true),
                ":vex" => Some(field(":vex").is_true()),
                // This deliberately mirrors the authored ACL2 definition:
                // both spellings test membership of :|256|.
                ":vex-256" | ":vex-128" => Some(
                    field(":vex").is_true()
                        && member(&WorldValue::Symbol(":256".into()), field(":vex")),
                ),
                ":evex" => Some(field(":evex").is_true()),
                ":no-vex" => Some(!field(":vex").is_true() && !field(":evex").is_true()),
                ":rex-w" => Some(field(":rex") == WorldValue::Symbol(":w".into())),
                _ => None,
            };
            if let Some(value) = special {
                return Ok(value);
            }
            if member(expr, field(":feat")) {
                return Ok(true);
            }
            Ok(matches!(
                mnemonic,
                WorldValue::String(ref name) if symbol.as_bytes().eq_ignore_ascii_case(name)
            ))
        }
        WorldValue::String(name) => Ok(matches!(
            mnemonic,
            WorldValue::String(ref candidate) if name.eq_ignore_ascii_case(candidate)
        )),
        WorldValue::List(_) | WorldValue::Cons(_, _) => {
            let expression = proper_list(expr.clone())?;
            let Some(WorldValue::Symbol(operator)) = expression.first() else {
                return Err(WorldError::Raised(format!(
                    "bad feature expression: {expr:?}"
                )));
            };
            let operands = &expression[1..];
            match operator.as_str() {
                "not" if operands.len() == 1 => Ok(!eval_feature_expr(&operands[0], inst)?),
                "and" => {
                    for operand in operands {
                        if !eval_feature_expr(operand, inst)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                "or" => {
                    for operand in operands {
                        if eval_feature_expr(operand, inst)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                "xor" => {
                    let mut value = false;
                    for operand in operands {
                        value ^= eval_feature_expr(operand, inst)?;
                    }
                    Ok(value)
                }
                _ => Err(WorldError::Raised(format!(
                    "bad feature expression: {expr:?}"
                ))),
            }
        }
        _ => Ok(expr.is_true()),
    }
}

/// Iterative execution counterpart of x86isa's recursive
/// `inst-list-prefix-byte-group-code`.
///
/// This is ordered read-time computation only. It derives each byte's group
/// from the authored instruction records and does not assert that the result
/// has any logical property.
fn iterative_inst_list_prefix_byte_group_code(
    args: Vec<WorldValue>,
) -> Result<WorldValue, WorldError> {
    let [
        WorldValue::Int(first_opcode),
        WorldValue::Int(num_opcodes),
        insts,
    ] = args.as_slice()
    else {
        return Err(WorldError::Arity("inst-list-prefix-byte-group-code"));
    };
    let count = usize::try_from(
        i64::try_from(num_opcodes)
            .map_err(|_| WorldError::Range("inst-list-prefix-byte-group-code"))?,
    )
    .map_err(|_| WorldError::Range("inst-list-prefix-byte-group-code"))?;
    let insts = proper_list(insts.clone())?;
    let mut opcode = first_opcode.clone();
    let mut output = Vec::with_capacity(count);
    for _ in 0..count {
        let mut matches = insts
            .iter()
            .filter(|inst| inst_opcode(inst).is_some_and(|candidate| candidate == &opcode));
        let first = matches.next();
        let unique = first.is_some() && matches.next().is_none();
        output.push(WorldValue::Int(Int::from(if unique {
            inst_prefix_byte_group_code(first.expect("checked"))
        } else {
            0
        })));
        opcode += Int::one();
    }
    Ok(WorldValue::list(output))
}

fn iterative_select_insts(args: Vec<WorldValue>) -> Result<WorldValue, WorldError> {
    let Some(insts) = args.first() else {
        return Err(WorldError::Arity("select-insts"));
    };
    if (args.len() - 1) % 2 != 0 {
        return Err(WorldError::Arity("select-insts"));
    }
    let mut options = BTreeMap::from([
        (":get/rem".to_string(), WorldValue::Symbol(":get".into())),
        (":opcode".to_string(), WorldValue::Nil),
        (":mode".to_string(), WorldValue::Nil),
        (":prefix".to_string(), WorldValue::Nil),
        (":vex?".to_string(), WorldValue::Nil),
        (":fn?".to_string(), WorldValue::Nil),
    ]);
    for pair in args[1..].chunks_exact(2) {
        let WorldValue::Symbol(keyword) = &pair[0] else {
            return Err(WorldError::Malformed("select-insts keyword"));
        };
        let Some(option) = options.get_mut(keyword) else {
            return Err(WorldError::UnknownMacroKeyword(
                "select-insts".into(),
                keyword.clone(),
            ));
        };
        *option = pair[1].clone();
    }
    let get = options[":get/rem"] == WorldValue::Symbol(":get".into());
    let opcode = &options[":opcode"];
    let mode = &options[":mode"];
    let prefix = &options[":prefix"];
    let vex = options[":vex?"].is_true();
    let function = options[":fn?"].is_true();
    let mut output = Vec::new();
    for inst in proper_list(insts.clone())? {
        let opcode_data = inst_opcode_record(&inst);
        let opcode_matches = !opcode.is_true()
            || opcode_data
                .as_ref()
                .and_then(|fields| keyword_field(fields, ":op"))
                == Some(opcode.clone());
        let mode_matches = !mode.is_true()
            || opcode_data
                .as_ref()
                .and_then(|fields| keyword_field(fields, ":mode"))
                == Some(mode.clone());
        let actual_prefix = opcode_data
            .as_ref()
            .and_then(|fields| keyword_field(fields, ":pfx"))
            .unwrap_or(WorldValue::Nil);
        let prefix_matches = if !prefix.is_true() {
            true
        } else if prefix == &WorldValue::Symbol(":no-prefix".into()) {
            actual_prefix == *prefix || !actual_prefix.is_true()
        } else {
            actual_prefix == *prefix
        };
        let vex_matches = !vex
            || opcode_data
                .as_ref()
                .and_then(|fields| keyword_field(fields, ":vex"))
                .is_some_and(|value| value.is_true());
        let function_matches = !function || inst_function(&inst).is_some_and(WorldValue::is_true);
        let matches =
            opcode_matches && mode_matches && prefix_matches && vex_matches && function_matches;
        if matches == get {
            output.push(inst);
        }
    }
    Ok(WorldValue::list(output))
}

fn iterative_filter_insts_with_feat(
    args: Vec<WorldValue>,
    keep: bool,
) -> Result<WorldValue, WorldError> {
    let [insts, features] = args.as_slice() else {
        return Err(WorldError::Arity(if keep {
            "keep-insts-with-feat"
        } else {
            "remove-insts-with-feat"
        }));
    };
    let features = proper_list(features.clone())?;
    let mut output = Vec::new();
    for inst in proper_list(insts.clone())? {
        let authored = inst_opcode_record(&inst)
            .as_ref()
            .and_then(|fields| keyword_field(fields, ":feat"))
            .and_then(|value| proper_list(value).ok())
            .unwrap_or_default();
        let present = features.iter().any(|feature| authored.contains(feature));
        if present == keep {
            output.push(inst);
        }
    }
    Ok(WorldValue::list(output))
}

fn iterative_opcode_present(args: Vec<WorldValue>) -> Result<WorldValue, WorldError> {
    let [
        WorldValue::Int(first_opcode),
        WorldValue::Int(num_opcodes),
        insts,
    ] = args.as_slice()
    else {
        return Err(WorldError::Arity("opcode-present?"));
    };
    let count = usize::try_from(
        i64::try_from(num_opcodes).map_err(|_| WorldError::Range("opcode-present?"))?,
    )
    .map_err(|_| WorldError::Range("opcode-present?"))?;
    let insts = proper_list(insts.clone())?;
    let mut opcode = first_opcode.clone();
    let mut output = Vec::with_capacity(count);
    for _ in 0..count {
        output.push(WorldValue::Int(Int::from(i64::from(insts.iter().any(
            |inst| inst_opcode(inst).is_some_and(|candidate| candidate == &opcode),
        )))));
        opcode += Int::one();
    }
    Ok(WorldValue::list(output))
}

fn inst_opcode_record(inst: &WorldValue) -> Option<Vec<WorldValue>> {
    let WorldValue::List(inst_fields) = inst else {
        return None;
    };
    proper_list(inst_fields.get(2)?.clone()).ok()
}

fn keyword_field(fields: &[WorldValue], keyword: &str) -> Option<WorldValue> {
    fields.windows(2).find_map(|pair| {
        (pair[0] == WorldValue::Symbol(keyword.into())).then(|| unquote_world(&pair[1]))
    })
}

fn inst_function(inst: &WorldValue) -> Option<&WorldValue> {
    let WorldValue::List(fields) = inst else {
        return None;
    };
    fields.get(4)
}

fn inst_opcode(inst: &WorldValue) -> Option<&Int> {
    let WorldValue::List(inst_fields) = inst else {
        return None;
    };
    let WorldValue::List(opcode_fields) = inst_fields.get(2)? else {
        return None;
    };
    opcode_fields.windows(2).find_map(|pair| {
        (pair[0] == WorldValue::Symbol(":op".into()))
            .then_some(&pair[1])
            .and_then(WorldValue::as_int)
    })
}

fn inst_prefix_byte_group_code(inst: &WorldValue) -> i64 {
    let WorldValue::List(fields) = inst else {
        return 0;
    };
    let Some(WorldValue::Symbol(mnemonic)) = fields.get(1) else {
        return 0;
    };
    match mnemonic.as_str() {
        ":prefix-lock" | ":prefix-repne" | ":prefix-rep/repe" => 1,
        ":prefix-es" | ":prefix-cs" | ":prefix-ss" | ":prefix-ds" | ":prefix-fs" | ":prefix-gs" => {
            2
        }
        ":prefix-opsize" => 3,
        ":prefix-addrsize" => 4,
        _ => 0,
    }
}

fn pre_opcode_map_names() -> [&'static str; 4] {
    [
        "*pre-one-byte-opcode-map*",
        "*pre-two-byte-opcode-map*",
        "*pre-0f-38-three-byte-opcode-map*",
        "*pre-0f-3a-three-byte-opcode-map*",
    ]
}

/// The reader folds unescaped ACL2 symbols to lowercase but preserves
/// `|escaped symbols|` verbatim. Hence any uppercase character marks a
/// case-preserved escaped spelling; fully lowercase spellings are the
/// canonicalized form of ordinary symbols and recover ACL2's uppercase name.
fn acl2_symbol_name(symbol: &str) -> String {
    if symbol.chars().any(char::is_uppercase) {
        symbol.to_string()
    } else {
        symbol.to_ascii_uppercase()
    }
}

fn int_list(value: &WorldValue) -> Option<Vec<i64>> {
    proper_list(value.clone())
        .ok()?
        .into_iter()
        .map(|value| i64::try_from(value.as_int()?).ok())
        .collect()
}

fn table_row_key(row: &WorldValue) -> Option<Vec<i64>> {
    match row {
        WorldValue::Cons(key, _) => int_list(key),
        WorldValue::List(parts) if parts.len() >= 2 => int_list(&parts[0]),
        _ => None,
    }
}

fn table_row_value(row: &WorldValue) -> Option<WorldValue> {
    match row {
        WorldValue::Cons(_, value) => Some((**value).clone()),
        WorldValue::List(parts) if parts.len() >= 2 => Some(WorldValue::List(parts[1..].to_vec())),
        _ => None,
    }
}

fn entry_instructions(entry: &WorldValue) -> Vec<WorldValue> {
    let mut output = Vec::new();
    for key in [":implemented", ":unimplemented"] {
        output.extend(entry_instruction_field(entry, key));
    }
    output
}

fn entry_instruction_field(entry: &WorldValue, key: &str) -> Vec<WorldValue> {
    let Ok(fields) = proper_list(entry.clone()) else {
        return vec![];
    };
    fields
        .windows(2)
        .find(|pair| pair[0] == WorldValue::Symbol(key.into()))
        .and_then(|pair| proper_list(pair[1].clone()).ok())
        .unwrap_or_default()
}

fn unquote_world(value: &WorldValue) -> WorldValue {
    let Ok(items) = proper_list(value.clone()) else {
        return value.clone();
    };
    if items.len() == 2 && items[0] == WorldValue::Symbol("quote".into()) {
        items[1].clone()
    } else {
        value.clone()
    }
}

/// ACL2's EQL agrees with structural equality on the scalar values represented
/// by this evaluator, but never equates separately constructed conses.
fn acl2_eql(left: &WorldValue, right: &WorldValue) -> bool {
    match (left, right) {
        (WorldValue::Nil, WorldValue::Nil)
        | (WorldValue::Int(_), WorldValue::Int(_))
        | (WorldValue::Symbol(_), WorldValue::Symbol(_))
        | (WorldValue::String(_), WorldValue::String(_)) => left == right,
        _ => false,
    }
}

fn acl2_character_byte(literal: &str) -> Option<u8> {
    let spelling = literal.strip_prefix("#\\")?;
    match spelling.to_ascii_lowercase().as_str() {
        "newline" | "linefeed" => Some(b'\n'),
        "space" => Some(b' '),
        "tab" => Some(b'\t'),
        "return" => Some(b'\r'),
        "page" => Some(12),
        "rubout" => Some(127),
        _ => {
            let mut chars = spelling.chars();
            let character = chars.next()?;
            if chars.next().is_some() {
                return None;
            }
            u8::try_from(u32::from(character)).ok()
        }
    }
}

fn acl2_subst(new: &WorldValue, old: &WorldValue, tree: &WorldValue) -> WorldValue {
    if acl2_eql(old, tree) {
        return new.clone();
    }
    match tree {
        WorldValue::List(values) => {
            WorldValue::list(values.iter().map(|value| acl2_subst(new, old, value)))
        }
        WorldValue::Cons(head, tail) => WorldValue::Cons(
            Box::new(acl2_subst(new, old, head)),
            Box::new(acl2_subst(new, old, tail)),
        ),
        _ => tree.clone(),
    }
}

fn define_return_names(returns: &WorldValue) -> Result<Vec<String>, WorldError> {
    let values = proper_list(returns.clone())?;
    let specs = if values.first() == Some(&WorldValue::Symbol("mv".into())) {
        &values[1..]
    } else {
        std::slice::from_ref(returns)
    };
    specs
        .iter()
        .map(|spec| match spec {
            WorldValue::Symbol(name) => Ok(name.clone()),
            WorldValue::List(values) => values
                .first()
                .and_then(|value| match value {
                    WorldValue::Symbol(name) => Some(name.clone()),
                    _ => None,
                })
                .ok_or(WorldError::Malformed("define :returns name")),
            _ => Err(WorldError::Malformed("define :returns spec")),
        })
        .collect()
}

fn spec_predicate_name(spec: &WorldValue) -> String {
    match spec {
        WorldValue::Symbol(name) => name.clone(),
        WorldValue::List(values) => values
            .first()
            .and_then(|value| match value {
                WorldValue::Symbol(name) => Some(name.clone()),
                _ => None,
            })
            .unwrap_or_else(|| "return".into()),
        _ => "return".into(),
    }
}

// ACL2's standard-analysis primitive type-set bit assignment from
// `type-set-a.lisp`.  The ordered world uses these values only as data while
// evaluating utilities such as `std::defenum`; they carry no logical
// authority.
fn acl2_type_set_quote(value: &WorldValue) -> i64 {
    match value {
        WorldValue::Nil => 1 << 7,
        WorldValue::Int(value) if value == &Int::zero() => 1,
        WorldValue::Int(value) if value == &Int::one() => 1 << 1,
        WorldValue::Int(value) if value.is_negative() => 1 << 4,
        WorldValue::Int(_) => 1 << 2,
        WorldValue::Symbol(value) if value == "t" => 1 << 8,
        WorldValue::Symbol(value) if acl2_character_byte(value).is_some() => 1 << 13,
        WorldValue::Symbol(_) => 1 << 9,
        WorldValue::String(_) => 1 << 12,
        WorldValue::List(_) => 1 << 10,
        WorldValue::Cons(_, tail) if proper_list((**tail).clone()).is_ok() => 1 << 10,
        WorldValue::Cons(_, _) => 1 << 11,
    }
}

fn quoted(value: WorldValue) -> WorldValue {
    WorldValue::list([WorldValue::Symbol("quote".into()), value])
}

fn world_call(head: &str, args: impl IntoIterator<Item = WorldValue>) -> WorldValue {
    WorldValue::list(std::iter::once(WorldValue::Symbol(head.into())).chain(args))
}

/// Exact ACL2 8.7 conversion for the two type sets produced by the x86isa
/// `defenum` calls.  Keeping this boundary explicit is important: an unknown
/// mask remains unresolved instead of manufacturing a weaker type theorem.
fn acl2_convert_enum_type_set(
    variable: &WorldValue,
    type_set: i64,
) -> Result<WorldValue, WorldError> {
    let equal_quoted = |value| world_call("equal", [variable.clone(), quoted(value)]);
    match type_set {
        // *TS-ZERO* union *TS-ONE*.  `disjoin` translates OR into IF.
        3 => Ok(world_call(
            "if",
            [
                equal_quoted(WorldValue::Int(Int::zero())),
                quoted(WorldValue::Symbol("t".into())),
                equal_quoted(WorldValue::Int(Int::one())),
            ],
        )),
        // *TS-NON-T-NON-NIL-SYMBOL*.  `conjoin` translates the three
        // inverter-rule terms into right-associated IFs.
        512 => {
            let not_t = world_call("not", [equal_quoted(WorldValue::Symbol("t".into()))]);
            let not_nil = world_call("not", [equal_quoted(WorldValue::Nil)]);
            Ok(world_call(
                "if",
                [
                    world_call("symbolp", [variable.clone()]),
                    world_call("if", [not_t, not_nil, quoted(WorldValue::Nil)]),
                    quoted(WorldValue::Nil),
                ],
            ))
        }
        other => Err(WorldError::UnsupportedOperation(format!(
            "acl2::convert-type-set-to-term mask {other}"
        ))),
    }
}

fn acl2_car(value: &WorldValue) -> WorldValue {
    match value {
        WorldValue::List(values) => values.first().cloned().unwrap_or(WorldValue::Nil),
        WorldValue::Cons(head, _) => (**head).clone(),
        _ => WorldValue::Nil,
    }
}

fn acl2_cdr(value: &WorldValue) -> WorldValue {
    match value {
        WorldValue::List(values) => WorldValue::list(values.iter().skip(1).cloned()),
        WorldValue::Cons(_, tail) => (**tail).clone(),
        _ => WorldValue::Nil,
    }
}

fn acl2_last(value: &WorldValue) -> WorldValue {
    match value {
        WorldValue::Nil => WorldValue::Nil,
        WorldValue::List(values) => values
            .last()
            .cloned()
            .map_or(WorldValue::Nil, |last| WorldValue::List(vec![last])),
        WorldValue::Cons(_, tail) => {
            if matches!(tail.as_ref(), WorldValue::Cons(_, _))
                || matches!(tail.as_ref(), WorldValue::List(values) if !values.is_empty())
            {
                acl2_last(tail)
            } else {
                value.clone()
            }
        }
        atom => atom.clone(),
    }
}

fn proper_list(value: WorldValue) -> Result<Vec<WorldValue>, WorldError> {
    if let WorldValue::List(values) = value {
        return Ok(values);
    }
    let mut output = Vec::new();
    let mut cursor = value;
    loop {
        match cursor {
            WorldValue::Nil => return Ok(output),
            WorldValue::Cons(head, tail) => {
                output.push(*head);
                cursor = *tail;
            }
            _ => return Err(WorldError::ImproperList),
        }
    }
}

fn take_quoted_defconst_progn(value: WorldValue) -> Result<Vec<(String, WorldValue)>, WorldValue> {
    let WorldValue::List(event) = value else {
        return Err(value);
    };
    if !matches!(event.first(), Some(WorldValue::Symbol(head)) if head == "progn") {
        return Err(WorldValue::List(event));
    }
    let recognized = event.iter().skip(1).all(|child| {
        let WorldValue::List(fields) = child else {
            return false;
        };
        fields.len() == 3
            && matches!(fields.first(), Some(WorldValue::Symbol(head)) if head == "defconst")
            && matches!(fields.get(1), Some(WorldValue::Symbol(_)))
            && matches!(
                fields.get(2),
                Some(WorldValue::List(quoted))
                    if quoted.len() == 2
                        && matches!(
                            quoted.first(),
                            Some(WorldValue::Symbol(head)) if head == "quote"
                        )
            )
    });
    if event.len() == 1 || !recognized {
        return Err(WorldValue::List(event));
    }
    let mut constants = Vec::with_capacity(event.len().saturating_sub(1));
    for child in event.into_iter().skip(1) {
        let WorldValue::List(mut fields) = child else {
            unreachable!("shape checked above");
        };
        let WorldValue::Symbol(name) = fields.remove(1) else {
            unreachable!("shape checked above");
        };
        let WorldValue::List(mut quoted) = fields.remove(1) else {
            unreachable!("shape checked above");
        };
        constants.push((name, quoted.remove(1)));
    }
    Ok(constants)
}

fn ints(args: Vec<WorldValue>) -> Result<Vec<Int>, WorldError> {
    args.into_iter()
        .map(|value| match value {
            WorldValue::Int(value) => Ok(value),
            _ => Err(WorldError::ExpectedInteger),
        })
        .collect()
}

fn int_fold(
    args: Vec<WorldValue>,
    initial: Int,
    operation: impl Fn(Int, &Int) -> Int,
) -> Result<WorldValue, WorldError> {
    Ok(WorldValue::Int(ints(args)?.iter().fold(initial, operation)))
}

fn unary_int(
    args: Vec<WorldValue>,
    operation: impl Fn(Int) -> Int,
) -> Result<WorldValue, WorldError> {
    let mut args = ints(args)?;
    if args.len() != 1 {
        return Err(WorldError::Arity("unary integer primitive"));
    }
    Ok(WorldValue::Int(operation(args.remove(0))))
}

fn binary_int(
    args: Vec<WorldValue>,
    operation: impl Fn(Int, Int) -> Int,
) -> Result<WorldValue, WorldError> {
    let mut args = ints(args)?;
    if args.len() != 2 {
        return Err(WorldError::Arity("binary integer primitive"));
    }
    let right = args.pop().expect("len checked");
    let left = args.pop().expect("len checked");
    Ok(WorldValue::Int(operation(left, right)))
}

fn compare_int(
    args: Vec<WorldValue>,
    operation: impl Fn(&Int, &Int) -> bool,
) -> Result<WorldValue, WorldError> {
    let args = ints(args)?;
    let [left, right] = args.as_slice() else {
        return Err(WorldError::Arity("integer comparison"));
    };
    Ok(WorldValue::truth(operation(left, right)))
}

fn usize_from_int(value: &Int, operation: &'static str) -> Result<usize, WorldError> {
    usize::try_from(i64::try_from(value).map_err(|_| WorldError::Range(operation))?)
        .map_err(|_| WorldError::Range(operation))
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum WorldError {
    #[error("malformed ACL2 world form: {0}")]
    Malformed(&'static str),
    #[error("unbound ACL2 world symbol `{0}`")]
    Unbound(String),
    #[error("unknown ACL2 world function `{0}`")]
    UnknownFunction(String),
    #[error("unsupported ACL2 macro: {0}")]
    UnsupportedMacro(String),
    #[error("unsupported ACL2 table operation: {0}")]
    UnsupportedTable(String),
    #[error("unsupported ACL2 world operation: {0}")]
    UnsupportedOperation(String),
    #[error("wrong arity for macro `{0}`")]
    MacroArity(String),
    #[error("unknown keyword `{1}` for macro `{0}`")]
    UnknownMacroKeyword(String, String),
    #[error("duplicate macro keyword `{0}`")]
    DuplicateMacroKeyword(String),
    #[error("wrong arity for `{0}`")]
    Arity(&'static str),
    #[error("expected an integer")]
    ExpectedInteger,
    #[error("expected a symbol, got {0}")]
    ExpectedSymbol(String),
    #[error("ACL2 raise: {0}")]
    Raised(String),
    #[error("integer out of range for `{0}`")]
    Range(&'static str),
    #[error("expected a proper list")]
    ImproperList,
    #[error("ACL2 world evaluation exhausted its fuel")]
    Fuel,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader::read_book;

    #[test]
    fn modrm_dispatch_walks_large_instruction_tables_without_recursing() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut world = Acl2World::new();
                world.constants.insert(
                    "*z-addressing-method-info*".into(),
                    WorldValue::list([
                        WorldValue::list([
                            WorldValue::Symbol("a".into()),
                            WorldValue::Cons(
                                Box::new(WorldValue::Symbol(":modr/m?".into())),
                                Box::new(WorldValue::Nil),
                            ),
                        ]),
                        WorldValue::list([
                            WorldValue::Symbol("e".into()),
                            WorldValue::Cons(
                                Box::new(WorldValue::Symbol(":modr/m?".into())),
                                Box::new(WorldValue::Symbol("t".into())),
                            ),
                        ]),
                    ]),
                );
                let instruction = |opcode: i64, method: &str| {
                    WorldValue::list([
                        WorldValue::Symbol("inst".into()),
                        WorldValue::String(b"STRESS".to_vec()),
                        WorldValue::list([
                            WorldValue::Symbol("op".into()),
                            WorldValue::Symbol(":op".into()),
                            WorldValue::Int(Int::from(opcode)),
                        ]),
                        WorldValue::list([
                            WorldValue::Symbol("arg".into()),
                            WorldValue::Symbol(":op1".into()),
                            WorldValue::list([
                                WorldValue::Symbol("quote".into()),
                                WorldValue::list([
                                    WorldValue::Symbol(method.into()),
                                    WorldValue::Symbol("v".into()),
                                ]),
                            ]),
                        ]),
                        WorldValue::Symbol("impl".into()),
                        WorldValue::Nil,
                    ])
                };
                let large =
                    WorldValue::list(std::iter::repeat_with(|| instruction(7, "a")).take(25_000));
                assert_eq!(
                    world.apply("any-inst-needs-modr/m-p", vec![large]).unwrap(),
                    WorldValue::Nil
                );
                let table = WorldValue::list([instruction(7, "e"), instruction(9, "a")]);
                assert_eq!(
                    world
                        .apply(
                            "compute-modr/m-for-opcodes",
                            vec![
                                WorldValue::Int(Int::from(7)),
                                WorldValue::Int(Int::from(3)),
                                table,
                            ],
                        )
                        .unwrap(),
                    WorldValue::list([
                        WorldValue::Int(Int::from(1)),
                        WorldValue::Int(Int::from(0)),
                        WorldValue::Int(Int::from(0)),
                    ])
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn ordered_constants_and_sharp_dot_are_computational_only() {
        let forms = read_book(
            "(defconst *byte-mask* (- (expt 2 8) 1))
             (defconst *bytes* (list #xF0 #b11 *byte-mask*))
             (defconst *low-nibble* (logand *byte-mask* #x0f))
             #.*byte-mask*
             (make-event `(defconst *nested-sharp-dot* ,#.*byte-mask*))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert!(world.process_event(&forms[1]).unwrap());
        assert!(world.process_event(&forms[2]).unwrap());
        assert_eq!(
            world.eval_sharp_dot(&forms[3]).unwrap(),
            WorldValue::Int(Int::from(255u64))
        );
        assert_eq!(
            proper_list(world.constant("*bytes*").unwrap().clone())
                .unwrap()
                .len(),
            3
        );
        assert_eq!(
            world.constant("*low-nibble*").unwrap().as_int(),
            Some(&Int::from(15u64))
        );
        assert_eq!(
            world.eval_make_event(&forms[4]).unwrap(),
            read_book("(defconst *nested-sharp-dot* 255)")
                .unwrap()
                .remove(0)
        );
    }

    #[test]
    fn make_event_can_install_quoted_defconsts() {
        let forms = read_book(
            "(defun generate ()
                `(defconsts (*a* *b* *len*)
                   ,(cons 'mv (append (increasing-list 4 2 2) (list 2)))))
             (make-event (generate))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        for form in &forms {
            assert!(world.process_event(form).unwrap());
        }
        assert_eq!(
            world.constant("*a*").unwrap().as_int(),
            Some(&Int::from(4u64))
        );
        assert_eq!(
            world.constant("*b*").unwrap().as_int(),
            Some(&Int::from(6u64))
        );
        assert_eq!(
            world.constant("*len*").unwrap().as_int(),
            Some(&Int::from(2u64))
        );
    }

    #[test]
    fn x86_world_list_membership_cadr_and_packn_preserve_acl2_values() {
        let forms = read_book(
            "(make-event
                `(defconst *member-tail* ',(member 'b '(a b c))))
             (make-event
                `(defconst *equal-tail* ',(member-equal '(b) '(a (b) c))))
             (make-event
                `(defconst *second* ',(cadr '(a b c))))
             (make-event
                `(defconst *packed*
                   ',(acl2::packn (list 'deserialize- 'x86::rgf 12))))
             (make-event
                `(defconst *removed* ',(remove 'b '(a b c b))))
             (make-event
                `(defconst *property*
                   ',(cadr (assoc-keyword :type
                                          '(:initially 0 :type (array 16))))))
             (make-event
                `(defconst *keyword* ',(intern \"RIP\" \"KEYWORD\")))
             (make-event
                `(defconst *array-length*
                   ',(caaddr '(array (unsigned-byte 8) (16)))))
             (make-event
                `(defconst *common-lisp-list-ops*
                   ',(list (first '(a b c))
                           (second '(a b c))
                           (rest '(a b c))
                           (cddr '(a b c))
                           (symbolp nil)
                           (symbolp \"not-a-symbol\")
                           (keywordp :type)
                           (keywordp 'type)
                           (assoc 'b '((a . 1) (b . 2)))
                           (acons 'c 3 '((a . 1)))
                           (cond ((keywordp :type) 'yes)
                                 (t 'no))
                           (acl2::subst 'y 'x '(f x (x z)))
                           (24bits-p 16777215)
                           (24bits-p 16777216))))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        let generated = forms
            .iter()
            .map(|form| world.eval_make_event(form).unwrap())
            .collect::<Vec<_>>();
        let expected = read_book(
            "(defconst *member-tail* '(b c))
             (defconst *equal-tail* '((b) c))
             (defconst *second* 'b)
             (defconst *packed* 'deserialize-rgf12)
             (defconst *removed* '(a c))
             (defconst *property* '(array 16))
             (defconst *keyword* ':rip)
             (defconst *array-length* '16)
             (defconst *common-lisp-list-ops*
               '(a b (b c) (c) t () t () (b . 2)
                 ((c . 3) (a . 1)) yes
                 (f y (y z)) t ()))",
        )
        .unwrap();
        assert_eq!(generated, expected);
    }

    #[test]
    fn pairlis_duplicates_and_character_literals_follow_acl2_execution() {
        let forms = read_book(
            "(make-event
                `(defconst *pairs*
                   ',(pairlis$ '(a b c) '(1 2))))
             (make-event
                `(defconst *duplicate-results*
                   ',(list (no-duplicatesp-equal '(a b c))
                           (no-duplicatesp-equal '(a (b) a))
                           (no-duplicatesp-equal '(a b . terminal)))))
             (make-event
                `(defconst *characters*
                   ',(list (string #\\Newline)
                           (string #\\A)
                           (characterp #\\Tab)
                           (symbolp #\\Tab)
                           (char-code #\\Rubout))))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        let generated = forms
            .iter()
            .map(|form| world.eval_make_event(form).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            generated,
            read_book(
                "(defconst *pairs* '((a . 1) (b . 2) (c)))
                 (defconst *duplicate-results* '(t () t))
                 (defconst *characters* '(\"\n\" \"A\" t () 127))"
            )
            .unwrap()
        );
    }

    #[test]
    fn defenum_type_set_primitives_match_acl2_87_terms() {
        let mut world = Acl2World::new();
        assert_eq!(
            world
                .apply(
                    "acl2::type-set-quote",
                    vec![WorldValue::Symbol("ordinary-symbol".into())],
                )
                .unwrap(),
            WorldValue::Int(Int::from(512u64))
        );
        assert_eq!(
            world
                .apply(
                    "acl2::type-set-quote",
                    vec![WorldValue::Symbol("#\\A".into())],
                )
                .unwrap(),
            WorldValue::Int(Int::from(8192u64))
        );

        let enabled = WorldValue::Symbol("acl2-enabled-structure".into());
        let acl2_world = WorldValue::Symbol("acl2-world".into());
        let x = WorldValue::Symbol("x".into());
        let symbol_term = world
            .apply(
                "acl2::convert-type-set-to-term",
                vec![
                    x.clone(),
                    WorldValue::Int(Int::from(512u64)),
                    enabled.clone(),
                    acl2_world.clone(),
                    WorldValue::Nil,
                ],
            )
            .unwrap();
        let bit_term = world
            .apply(
                "acl2::convert-type-set-to-term",
                vec![
                    x,
                    WorldValue::Int(Int::from(3u64)),
                    enabled,
                    acl2_world,
                    WorldValue::Nil,
                ],
            )
            .unwrap();
        assert_eq!(
            symbol_term,
            quote(
                &read_book(
                    "((if (symbolp x)
                           (if (not (equal x 't))
                               (not (equal x 'nil))
                             'nil)
                         'nil)
                       nil)"
                )
                .unwrap()[0]
            )
            .unwrap()
        );
        assert_eq!(
            bit_term,
            quote(
                &read_book(
                    "((if (equal x '0)
                           't
                         (equal x '1))
                       nil)"
                )
                .unwrap()[0]
            )
            .unwrap()
        );
        assert!(matches!(
            world.apply(
                "acl2::convert-type-set-to-term",
                vec![
                    WorldValue::Symbol("x".into()),
                    WorldValue::Int(Int::from(4096u64)),
                    WorldValue::Symbol("acl2-enabled-structure".into()),
                    WorldValue::Symbol("acl2-world".into()),
                    WorldValue::Nil,
                ],
            ),
            Err(WorldError::UnsupportedOperation(_))
        ));
    }

    #[test]
    fn defund_helpers_are_available_to_later_make_events() {
        let forms = read_book(
            "(defund enum-tests (members x)
                (if (atom members)
                    nil
                  (cons (list 'equal x (list 'quote (car members)))
                        (enum-tests (cdr members) x))))
             (make-event
                `(defconst *enum-tests*
                   ',(enum-tests '(a b) 'x)))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.eval_make_event(&forms[1]).unwrap(),
            read_book("(defconst *enum-tests* '((equal x 'a) (equal x 'b)))")
                .unwrap()
                .remove(0)
        );
    }

    #[test]
    fn x86_save_restore_list_star_binder_destructures_flat_lists() {
        let forms = read_book(
            "(defun collect-types (fields)
                (b* (((when (not fields)) nil)
                     ((list* field tail) fields))
                  (cons (cadr field) (collect-types tail))))
             (make-event
                `(defconst *types*
                   ',(collect-types '((ms :scalar) (rgf :array)))))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.eval_make_event(&forms[1]).unwrap(),
            read_book("(defconst *types* '(:scalar :array))")
                .unwrap()
                .remove(0)
        );
    }

    #[test]
    fn generated_event_strings_modes_comparisons_and_catalogue_binders_are_bounded() {
        let forms = read_book(
            "(defun catalogue-doc (table)
                (b* (((cons section (sdm-instruction-table-entry entry))
                      (car table)))
                  (list section
                        entry.title
                        entry.implemented
                        entry.unimplemented
                        entry.doc
                        entry.subsecs)))
             (make-event
               `(defconst *bounded-world-primitives*
                  ',(list (concatenate 'string \"MAKE-\" \"FOO\")
                          (str::cat \"MODE-\" (str::nat-to-dec-string 64))
                          (default-defun-mode (w state))
                          (< 2 3)
                          (>= 3 3)
                          (case 15
                            ((8 16) 'wrong)
                            (15 'fifteen)
                            (otherwise 'wrong))
                          (car (last '(a b c)))
                          (intern-in-package-of-symbol \"BAR\" 'pkg::foo)
                          (function-symbolp 'catalogue-doc (w state))
                          (if (and (supported-platform?)
                                   (function-symbolp 'missing (w state)))
                              (value 'host)
                            (value 'fallback))
                          (catalogue-doc
                            (acons '(5 1)
                                   (make-sdm-instruction-table-entry
                                     :title \"Data\"
                                     :implemented '(add)
                                     :unimplemented '(sub)
                                     :doc \"doc\"
                                     :subsecs nil)
                                   nil)))))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.eval_make_event(&forms[1]).unwrap(),
            read_book(
                "(defconst *bounded-world-primitives*
                   '(\"MAKE-FOO\" \"MODE-64\" :logic t t fifteen c pkg::bar t
                     (() fallback state)
                     ((5 1) \"Data\" (add) (sub) \"doc\" ())))"
            )
            .unwrap()
            .remove(0)
        );
    }

    #[test]
    fn str_implode_preserves_exact_acl2_character_bytes() {
        let forms = read_book(
            "(defconst *nl* (str::implode (list #\\Newline)))
             (make-event
               `(defconst *padding*
                  ,(str::implode
                     (list #\\Newline #\\Space #\\A #\\Tab #\\Rubout))))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.constant("*nl*"),
            Some(&WorldValue::String(vec![b'\n']))
        );
        assert_eq!(
            world.eval_make_event(&forms[1]).unwrap(),
            read_book("(defconst *padding* \"\n A\t\u{7f}\")")
                .unwrap()
                .remove(0)
        );
    }

    #[test]
    fn bstar_control_binder_accepts_authored_multi_form_exit_body() {
        let forms = read_book(
            "(defun checked (ok)
                (b* (((unless ok)
                      'ignored-side-value
                      '(bad value)))
                  '(good value)))
             (make-event
                `(defconst *checked*
                   ',(list (checked t) (checked nil))))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.eval_make_event(&forms[1]).unwrap(),
            read_book("(defconst *checked* '((good value) (bad value)))")
                .unwrap()
                .remove(0)
        );
    }

    #[test]
    fn acl2_formals_queries_only_registered_signatures_in_the_state_world() {
        let forms = read_book(
            "(defun read-byte (addr x86) (list addr x86))
             (make-event
                `(defconst *read-byte-formals*
                   ',(acl2::formals 'read-byte (w state))))
             (make-event `(defconst *bad-world* ,(w 'not-state)))
             (make-event
                `(defconst *unknown-formals*
                   ',(acl2::formals 'missing (w state))))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.eval_make_event(&forms[1]).unwrap(),
            read_book("(defconst *read-byte-formals* '(addr x86))")
                .unwrap()
                .remove(0)
        );
        assert!(matches!(
            world.eval_make_event(&forms[2]),
            Err(WorldError::Malformed("w state"))
        ));
        assert!(matches!(
            world.eval_make_event(&forms[3]),
            Err(WorldError::UnknownFunction(name)) if name == "missing"
        ));
    }

    #[test]
    fn defret_uses_retained_define_guts_to_emit_exact_theorem_formula() {
        let forms = read_book(
            "(define split ((x natp))
                :returns (mv (left natp) (right natp))
                (mv x x)
                ///
                (defret <fn>-bounded
                  (<= right x)
                  :rule-classes :linear))
             (make-event
                (defret-fn '<fn>-bounded
                           '((<= right x) :rule-classes :linear)
                           nil
                           (w state)))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.eval_make_event(&forms[1]).unwrap(),
            read_book(
                "(defthm split-bounded
                   (b* (((mv ?left ?right) (split x)))
                     (<= right x))
                   :rule-classes :linear)"
            )
            .unwrap()
            .remove(0)
        );
    }

    #[test]
    fn more_returns_uses_retained_multi_value_signature() {
        let forms = read_book(
            "(define decode ((x natp))
                :returns (mv flg (disp natp))
                (mv nil x)
                ///
                (more-returns
                  (disp integerp
                        :hyp (natp x)
                        :name decode-disp-integerp
                        :rule-classes :type-prescription)))
             (make-event
                (more-returns-fn
                  '((disp integerp
                          :hyp (natp x)
                          :name decode-disp-integerp
                          :rule-classes :type-prescription))
                  (w state)))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.eval_make_event(&forms[1]).unwrap(),
            read_book(
                "(progn
                   (defthm decode-disp-integerp
                     (b* (((mv ?flg ?disp) (decode x)))
                       (implies (natp x) (integerp disp)))
                     :rule-classes :type-prescription))"
            )
            .unwrap()
            .remove(0)
        );
    }

    #[test]
    fn make_event_mv_let_binds_values_and_unwraps_error_value_state() {
        let forms = read_book(
            "(make-event
               (mv-let (erp map state)
                   (mv nil '((inst \"ADD\" (op :op 0))) state)
                 (mv erp
                     `(defconst *opcode-map* ',map)
                     state)))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert_eq!(
            world.eval_make_event(&forms[0]).unwrap(),
            read_book("(defconst *opcode-map* '((inst \"ADD\" (op :op 0))))")
                .unwrap()
                .remove(0)
        );
    }

    #[test]
    fn x86_opcode_finalizer_installs_flat_generated_maps() {
        let forms = read_book(
            "(defconst *pre-one-byte-opcode-map*
                '((inst \"ADD\" (op :op 0))))
             (defconst *pre-two-byte-opcode-map* '())
             (defconst *pre-0f-38-three-byte-opcode-map* '())
             (defconst *pre-0f-3a-three-byte-opcode-map* '())
             (make-event
               (mv-let (one-byte-opcode-map
                        two-byte-opcode-map
                        0f-38-three-byte-opcode-map
                        0f-3a-three-byte-opcode-map
                        state)
                 (eval-pre-map-recursively state)
                 (mv nil
                     `(progn
                        (defconst *one-byte-opcode-map*
                          ',one-byte-opcode-map)
                        (defconst *two-byte-opcode-map*
                          ',two-byte-opcode-map)
                        (defconst *0f-38-three-byte-opcode-map*
                          ',0f-38-three-byte-opcode-map)
                        (defconst *0f-3a-three-byte-opcode-map*
                          ',0f-3a-three-byte-opcode-map))
                     state)))",
        )
        .unwrap();
        let mut world = Acl2World::new();
        for form in &forms[..4] {
            assert!(world.process_event(form).unwrap());
        }
        assert_eq!(
            world.eval_make_event(&forms[4]).unwrap(),
            read_book(
                "(progn
                   (defconst *one-byte-opcode-map*
                     '((inst \"ADD\" (op :op 0))))
                   (defconst *two-byte-opcode-map* '())
                   (defconst *0f-38-three-byte-opcode-map* '())
                   (defconst *0f-3a-three-byte-opcode-map* '()))"
            )
            .unwrap()
            .remove(0)
        );
    }

    #[test]
    fn x86_opcode_consumers_iterate_over_flat_maps_exactly() {
        let forms = read_book(
            "(defconst *map*
                '((inst :prefix-lock (op :op 240) nil nil nil)
                  (inst \"MODE\" (op :op 15 :mode :i64 :pfx :66
                                           :feat '(:avx)) nil impl nil)
                  (inst \"NOP\" (op :op 15) nil nil nil)))
             (select-insts *map* :opcode 15)
             (select-insts *map* :get/rem :rem :mode :i64)
             (select-insts *map* :prefix :no-prefix)
             (keep-insts-with-feat *map* '(:avx))
             (remove-insts-with-feat *map* '(:avx))
             (opcode-present? 14 3 *map*)
             (inst-list-prefix-byte-group-code 240 1 *map*)",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());

        let expected = read_book(
            "'(((inst \"MODE\" (op :op 15 :mode :i64 :pfx :66
                                      :feat '(:avx)) nil impl nil)
                (inst \"NOP\" (op :op 15) nil nil nil))
               ((inst :prefix-lock (op :op 240) nil nil nil)
                (inst \"NOP\" (op :op 15) nil nil nil))
               ((inst :prefix-lock (op :op 240) nil nil nil)
                (inst \"NOP\" (op :op 15) nil nil nil))
               ((inst \"MODE\" (op :op 15 :mode :i64 :pfx :66
                                      :feat '(:avx)) nil impl nil))
               ((inst :prefix-lock (op :op 240) nil nil nil)
                (inst \"NOP\" (op :op 15) nil nil nil))
               (0 1 0)
               (1))",
        )
        .unwrap()
        .remove(0);
        let expected = quote(
            list(&expected)
                .and_then(|items| items.get(1))
                .expect("quoted expected values"),
        )
        .unwrap();
        let actual = WorldValue::list(
            forms[1..]
                .iter()
                .map(|form| world.eval_root(form))
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn quasiquoted_macros_expand_required_and_rest_arguments() {
        let forms = read_book(
            "(defmacro define-pair (name left &rest right)
                `(defconst ,name (list ,left ,@right)))
             (define-pair *pair* #x10 20 30)",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        let expanded = world.expand_macro_call(&forms[1]).unwrap().unwrap();
        assert_eq!(
            expanded,
            read_book("(defconst *pair* (list 16 20 30))")
                .unwrap()
                .remove(0)
        );
    }

    #[test]
    fn key_macros_apply_quoted_defaults_and_reject_unknown_keywords() {
        let forms = read_book(
            "(defmacro computational (x) (cons 'list x))
             (defmacro keyed (x &key (y 'nil)) `(list ,x ,y))
             (keyed a :y b)
             (keyed a :unknown b)",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(matches!(
            world.process_event(&forms[0]),
            Err(WorldError::UnsupportedMacro(_))
        ));
        assert!(world.process_event(&forms[1]).unwrap());
        assert_eq!(
            world.expand_macro_call(&forms[2]).unwrap().unwrap(),
            read_book("(list a b)").unwrap().remove(0)
        );
        assert!(matches!(
            world.expand_macro_call(&forms[3]),
            Err(WorldError::UnknownMacroKeyword(_, _))
        ));
    }

    #[test]
    fn constant_macro_body_is_safe_event_data() {
        let forms = read_book("(defmacro supported-platform? () t) (supported-platform?)").unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.expand_macro_call(&forms[1]).unwrap(),
            Some(SExpr::symbol("t"))
        );
    }

    #[test]
    fn macro_optional_and_guarded_keys_bind_supplied_flags() {
        let forms = read_book(
            "(defmacro advanced (name
                                  &optional (suffix 'nil suffix-p)
                                  &key
                                  ((body true-listp) 'nil body-p)
                                  ((:enabled enabledp) 'nil enabled-supplied-p))
                `(progn
                   ,@(and suffix-p `((table suffix ',suffix)))
                   ,@(and body-p `((table body ',body)))
                   ,@(and enabled-supplied-p `((table enabled ',enabledp)))
                   (defthm ,name t)))
             (advanced sample extra :body (one two) :enabled t)
             (advanced minimal)",
        )
        .unwrap();
        let mut world = Acl2World::new();
        assert!(world.process_event(&forms[0]).unwrap());
        assert_eq!(
            world.expand_macro_call(&forms[1]).unwrap().unwrap(),
            read_book(
                "(progn
                   (table suffix 'extra)
                   (table body '(one two))
                   (table enabled 't)
                   (defthm sample t))"
            )
            .unwrap()
            .remove(0)
        );
        assert_eq!(
            world.expand_macro_call(&forms[2]).unwrap().unwrap(),
            read_book("(progn (defthm minimal t))").unwrap().remove(0)
        );
    }

    /// Run with `ACL2_X86ISA_DIR=/path/to/books/projects/x86isa cargo test
    /// -p covalence-lisp portcullis_constant_world --features hol -- --ignored`.
    #[test]
    #[ignore = "requires a separately downloaded ACL2 x86isa corpus"]
    fn portcullis_constant_world() {
        let root = std::path::PathBuf::from(
            std::env::var_os("ACL2_X86ISA_DIR").expect("set ACL2_X86ISA_DIR"),
        );
        let mut world = Acl2World::new();
        for relative in [
            "portcullis/utils.lisp",
            "portcullis/sharp-dot-defuns.lisp",
            "portcullis/sharp-dot-constants.lisp",
        ] {
            let source = std::fs::read_to_string(root.join(relative)).unwrap();
            for (index, event) in read_book(&source).unwrap().iter().enumerate() {
                world
                    .process_event(event)
                    .unwrap_or_else(|error| panic!("{relative}: event {}: {error}", index + 1));
            }
        }
        assert_eq!(
            world.constant("*2^512*").and_then(WorldValue::as_int),
            Some(&Int::from(2u64).pow(512))
        );
        assert_eq!(
            world
                .constant("*segment-register-names-len*")
                .and_then(WorldValue::as_int),
            Some(&Int::from(6u64))
        );
        assert_eq!(
            world.constant("*ia32_efer*").and_then(WorldValue::as_int),
            Some(&"3221225600".parse::<Int>().unwrap())
        );
    }

    #[test]
    #[ignore = "requires a separately downloaded ACL2 x86isa corpus"]
    fn def_inst_expands_a_scalar_instruction_template() {
        let root = std::path::PathBuf::from(
            std::env::var_os("ACL2_X86ISA_DIR").expect("set ACL2_X86ISA_DIR"),
        );
        let definitions = read_book(
            &std::fs::read_to_string(root.join("machine/decoding-and-spec-utils.lisp")).unwrap(),
        )
        .unwrap();
        let definition = definitions
            .iter()
            .find(|form| {
                list(form).is_some_and(|items| {
                    items.first().and_then(symbol) == Some("defmacro")
                        && items.get(1).and_then(symbol) == Some("def-inst")
                })
            })
            .expect("def-inst definition");
        let calls = read_book(
            &std::fs::read_to_string(root.join("machine/instructions/cache.lisp")).unwrap(),
        )
        .unwrap();
        let call = calls
            .iter()
            .find(|form| {
                list(form).and_then(|items| items.first()).and_then(symbol) == Some("def-inst")
            })
            .expect("x86-invlpg def-inst call");
        let mut world = Acl2World::new();
        assert!(world.process_event(definition).unwrap());
        let expanded = world.expand_macro_call(call).unwrap().unwrap();
        let items = list(&expanded).expect("expanded event");
        assert_eq!(items.first().and_then(symbol), Some("define"));
        assert_eq!(items.get(1).and_then(symbol), Some("x86-invlpg"));
        assert!(
            items.iter().any(|item| symbol(item) == Some(":returns")),
            "keyword metadata must survive faithful expansion"
        );
    }
}
