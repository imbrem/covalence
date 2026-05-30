use pyo3::IntoPyObjectExt;
use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyTuple};

use covalence_wasm::val;

/// Component model value type descriptor.
#[pyclass(name = "ValType", from_py_object)]
#[derive(Clone)]
pub struct PyValType {
    pub(crate) inner: val::ValType,
}

#[pymethods]
impl PyValType {
    // -- Primitive constructors -----------------------------------------------

    #[staticmethod]
    fn bool() -> Self {
        Self {
            inner: val::ValType::Bool,
        }
    }

    #[staticmethod]
    fn s8() -> Self {
        Self {
            inner: val::ValType::S8,
        }
    }

    #[staticmethod]
    fn u8() -> Self {
        Self {
            inner: val::ValType::U8,
        }
    }

    #[staticmethod]
    fn s16() -> Self {
        Self {
            inner: val::ValType::S16,
        }
    }

    #[staticmethod]
    fn u16() -> Self {
        Self {
            inner: val::ValType::U16,
        }
    }

    #[staticmethod]
    fn s32() -> Self {
        Self {
            inner: val::ValType::S32,
        }
    }

    #[staticmethod]
    fn u32() -> Self {
        Self {
            inner: val::ValType::U32,
        }
    }

    #[staticmethod]
    fn s64() -> Self {
        Self {
            inner: val::ValType::S64,
        }
    }

    #[staticmethod]
    fn u64() -> Self {
        Self {
            inner: val::ValType::U64,
        }
    }

    #[staticmethod]
    fn f32() -> Self {
        Self {
            inner: val::ValType::F32,
        }
    }

    #[staticmethod]
    fn f64() -> Self {
        Self {
            inner: val::ValType::F64,
        }
    }

    #[staticmethod]
    fn v128() -> Self {
        Self {
            inner: val::ValType::V128,
        }
    }

    #[staticmethod]
    fn char() -> Self {
        Self {
            inner: val::ValType::Char,
        }
    }

    #[staticmethod]
    fn string() -> Self {
        Self {
            inner: val::ValType::String,
        }
    }

    // -- Compound constructors ------------------------------------------------

    #[staticmethod]
    fn list(elem: &PyValType) -> Self {
        Self {
            inner: val::ValType::List(Box::new(elem.inner.clone())),
        }
    }

    #[staticmethod]
    fn record(fields: Vec<(String, PyValType)>) -> Self {
        Self {
            inner: val::ValType::Record(fields.into_iter().map(|(k, v)| (k, v.inner)).collect()),
        }
    }

    #[staticmethod]
    fn tuple(items: Vec<PyValType>) -> Self {
        Self {
            inner: val::ValType::Tuple(items.into_iter().map(|v| v.inner).collect()),
        }
    }

    #[staticmethod]
    fn variant(cases: Vec<(String, Option<PyValType>)>) -> Self {
        Self {
            inner: val::ValType::Variant(
                cases
                    .into_iter()
                    .map(|(k, v)| (k, v.map(|t| t.inner)))
                    .collect(),
            ),
        }
    }

    #[staticmethod]
    fn enum_(cases: Vec<String>) -> Self {
        Self {
            inner: val::ValType::Enum(cases),
        }
    }

    #[staticmethod]
    fn option(inner: &PyValType) -> Self {
        Self {
            inner: val::ValType::Option(Box::new(inner.inner.clone())),
        }
    }

    #[staticmethod]
    #[pyo3(signature = (*, ok=None, err=None))]
    fn result(ok: Option<&PyValType>, err: Option<&PyValType>) -> Self {
        Self {
            inner: val::ValType::Result {
                ok: ok.map(|t| Box::new(t.inner.clone())),
                err: err.map(|t| Box::new(t.inner.clone())),
            },
        }
    }

    #[staticmethod]
    fn flags(names: Vec<String>) -> Self {
        Self {
            inner: val::ValType::Flags(names),
        }
    }

    // -- Accessors ------------------------------------------------------------

    #[getter]
    fn kind(&self) -> &'static str {
        self.inner.kind()
    }

    fn __repr__(&self) -> String {
        format!("ValType({})", self.inner)
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __eq__(&self, other: &PyValType) -> bool {
        self.inner == other.inner
    }
}

/// Concrete component model value.
#[pyclass(name = "Val", from_py_object)]
#[derive(Clone)]
pub struct PyVal {
    pub(crate) inner: val::Val,
}

#[pymethods]
impl PyVal {
    // -- Primitive constructors -----------------------------------------------

    #[staticmethod]
    #[pyo3(name = "bool")]
    fn bool_(v: bool) -> Self {
        Self {
            inner: val::Val::Bool(v),
        }
    }

    #[staticmethod]
    fn s8(v: i8) -> Self {
        Self {
            inner: val::Val::S8(v),
        }
    }

    #[staticmethod]
    #[pyo3(name = "u8")]
    fn u8_(v: u8) -> Self {
        Self {
            inner: val::Val::U8(v),
        }
    }

    #[staticmethod]
    fn s16(v: i16) -> Self {
        Self {
            inner: val::Val::S16(v),
        }
    }

    #[staticmethod]
    #[pyo3(name = "u16")]
    fn u16_(v: u16) -> Self {
        Self {
            inner: val::Val::U16(v),
        }
    }

    #[staticmethod]
    fn s32(v: i32) -> Self {
        Self {
            inner: val::Val::S32(v),
        }
    }

    #[staticmethod]
    #[pyo3(name = "u32")]
    fn u32_(v: u32) -> Self {
        Self {
            inner: val::Val::U32(v),
        }
    }

    #[staticmethod]
    fn s64(v: i64) -> Self {
        Self {
            inner: val::Val::S64(v),
        }
    }

    #[staticmethod]
    #[pyo3(name = "u64")]
    fn u64_(v: u64) -> Self {
        Self {
            inner: val::Val::U64(v),
        }
    }

    #[staticmethod]
    #[pyo3(name = "f32")]
    fn f32_(v: f32) -> Self {
        Self {
            inner: val::Val::F32(v),
        }
    }

    #[staticmethod]
    #[pyo3(name = "f64")]
    fn f64_(v: f64) -> Self {
        Self {
            inner: val::Val::F64(v),
        }
    }

    #[staticmethod]
    fn v128(v: u128) -> Self {
        Self {
            inner: val::Val::V128(v),
        }
    }

    #[staticmethod]
    #[pyo3(name = "char")]
    fn char_(v: char) -> Self {
        Self {
            inner: val::Val::Char(v),
        }
    }

    #[staticmethod]
    fn string(v: String) -> Self {
        Self {
            inner: val::Val::String(v),
        }
    }

    // -- Compound constructors ------------------------------------------------

    #[staticmethod]
    fn list(items: Vec<PyVal>) -> Self {
        Self {
            inner: val::Val::List(items.into_iter().map(|v| v.inner).collect()),
        }
    }

    #[staticmethod]
    fn record(fields: &Bound<'_, PyDict>) -> PyResult<Self> {
        let mut out = Vec::with_capacity(fields.len());
        for (k, v) in fields.iter() {
            let key: String = k.extract()?;
            let val: PyVal = v.extract()?;
            out.push((key, val.inner));
        }
        Ok(Self {
            inner: val::Val::Record(out),
        })
    }

    #[staticmethod]
    fn tuple(items: Vec<PyVal>) -> Self {
        Self {
            inner: val::Val::Tuple(items.into_iter().map(|v| v.inner).collect()),
        }
    }

    #[staticmethod]
    #[pyo3(signature = (case, payload=None))]
    fn variant(case: String, payload: Option<PyVal>) -> Self {
        Self {
            inner: val::Val::Variant {
                case,
                payload: payload.map(|v| Box::new(v.inner)),
            },
        }
    }

    #[staticmethod]
    fn enum_(case: String) -> Self {
        Self {
            inner: val::Val::Enum(case),
        }
    }

    /// Construct a `some(val)` option value.
    #[staticmethod]
    fn option(val: PyVal) -> Self {
        Self {
            inner: val::Val::Option(Some(Box::new(val.inner))),
        }
    }

    /// Construct a `none` option value.
    #[staticmethod]
    fn none() -> Self {
        Self {
            inner: val::Val::Option(None),
        }
    }

    /// Construct an `ok(val)` result. Pass `None` for unit ok.
    #[staticmethod]
    #[pyo3(signature = (val=None))]
    fn ok(val: Option<PyVal>) -> Self {
        Self {
            inner: val::Val::Result(Ok(val.map(|v| Box::new(v.inner)))),
        }
    }

    /// Construct an `err(val)` result. Pass `None` for unit err.
    #[staticmethod]
    #[pyo3(signature = (val=None))]
    fn err(val: Option<PyVal>) -> Self {
        Self {
            inner: val::Val::Result(Err(val.map(|v| Box::new(v.inner)))),
        }
    }

    #[staticmethod]
    fn flags(names: Vec<String>) -> Self {
        Self {
            inner: val::Val::Flags(names),
        }
    }

    // -- Accessors ------------------------------------------------------------

    #[getter]
    fn kind(&self) -> &'static str {
        self.inner.kind()
    }

    #[getter]
    fn val_type(&self) -> PyValType {
        PyValType {
            inner: self.inner.val_type(),
        }
    }

    fn conforms_to(&self, ty: &PyValType) -> bool {
        self.inner.conforms_to(&ty.inner)
    }

    fn __repr__(&self) -> String {
        format!("Val({})", self.inner)
    }

    fn __str__(&self) -> String {
        self.inner.to_string()
    }

    fn __eq__(&self, other: &PyVal) -> bool {
        self.inner == other.inner
    }

    // -- Conversion -----------------------------------------------------------

    /// Convert this Val to a native Python value.
    fn to_python<'py>(&self, py: Python<'py>) -> PyResult<Py<PyAny>> {
        val_to_python(py, &self.inner)
    }

    /// Construct a Val from a native Python value, guided by a ValType.
    #[staticmethod]
    fn from_python(ty: &PyValType, obj: &Bound<'_, PyAny>) -> PyResult<Self> {
        let inner = val_from_python(&ty.inner, obj)?;
        Ok(Self { inner })
    }
}

fn val_to_python(py: Python<'_>, val: &val::Val) -> PyResult<Py<PyAny>> {
    Ok(match val {
        val::Val::Bool(v) => v.into_py_any(py)?,
        val::Val::S8(v) => v.into_py_any(py)?,
        val::Val::U8(v) => v.into_py_any(py)?,
        val::Val::S16(v) => v.into_py_any(py)?,
        val::Val::U16(v) => v.into_py_any(py)?,
        val::Val::S32(v) => v.into_py_any(py)?,
        val::Val::U32(v) => v.into_py_any(py)?,
        val::Val::S64(v) => v.into_py_any(py)?,
        val::Val::U64(v) => v.into_py_any(py)?,
        val::Val::F32(v) => v.into_py_any(py)?,
        val::Val::F64(v) => v.into_py_any(py)?,
        val::Val::V128(v) => v.into_py_any(py)?,
        val::Val::Char(v) => v.to_string().into_py_any(py)?,
        val::Val::String(v) => v.into_py_any(py)?,
        val::Val::List(items) => {
            let elems = items
                .iter()
                .map(|v| val_to_python(py, v))
                .collect::<PyResult<Vec<_>>>()?;
            PyList::new(py, elems)?.into_any().unbind()
        }
        val::Val::Record(fields) => {
            let dict = PyDict::new(py);
            for (k, v) in fields {
                dict.set_item(k, val_to_python(py, v)?)?;
            }
            dict.into_any().unbind()
        }
        val::Val::Tuple(items) => {
            let elems = items
                .iter()
                .map(|v| val_to_python(py, v))
                .collect::<PyResult<Vec<_>>>()?;
            PyTuple::new(py, elems)?.into_any().unbind()
        }
        val::Val::Variant { case, payload } => {
            let dict = PyDict::new(py);
            dict.set_item("case", case)?;
            match payload {
                Some(v) => dict.set_item("payload", val_to_python(py, v)?)?,
                None => dict.set_item("payload", py.None())?,
            }
            dict.into_any().unbind()
        }
        val::Val::Enum(case) => case.into_py_any(py)?,
        val::Val::Option(inner) => match inner {
            Some(v) => val_to_python(py, v)?,
            None => py.None(),
        },
        val::Val::Result(r) => {
            let dict = PyDict::new(py);
            match r {
                Ok(v) => {
                    dict.set_item("ok", true)?;
                    match v {
                        Some(val) => dict.set_item("value", val_to_python(py, val)?)?,
                        None => dict.set_item("value", py.None())?,
                    }
                }
                Err(v) => {
                    dict.set_item("ok", false)?;
                    match v {
                        Some(val) => dict.set_item("value", val_to_python(py, val)?)?,
                        None => dict.set_item("value", py.None())?,
                    }
                }
            }
            dict.into_any().unbind()
        }
        val::Val::Flags(flags) => {
            let elems = flags
                .iter()
                .map(|f| f.into_py_any(py))
                .collect::<PyResult<Vec<_>>>()?;
            PyList::new(py, elems)?.into_any().unbind()
        }
    })
}

fn val_from_python(ty: &val::ValType, obj: &Bound<'_, PyAny>) -> PyResult<val::Val> {
    match ty {
        val::ValType::Bool => {
            let v: bool = obj.extract()?;
            Ok(val::Val::Bool(v))
        }
        val::ValType::S8 => {
            let v: i8 = obj.extract()?;
            Ok(val::Val::S8(v))
        }
        val::ValType::U8 => {
            let v: u8 = obj.extract()?;
            Ok(val::Val::U8(v))
        }
        val::ValType::S16 => {
            let v: i16 = obj.extract()?;
            Ok(val::Val::S16(v))
        }
        val::ValType::U16 => {
            let v: u16 = obj.extract()?;
            Ok(val::Val::U16(v))
        }
        val::ValType::S32 => {
            let v: i32 = obj.extract()?;
            Ok(val::Val::S32(v))
        }
        val::ValType::U32 => {
            let v: u32 = obj.extract()?;
            Ok(val::Val::U32(v))
        }
        val::ValType::S64 => {
            let v: i64 = obj.extract()?;
            Ok(val::Val::S64(v))
        }
        val::ValType::U64 => {
            let v: u64 = obj.extract()?;
            Ok(val::Val::U64(v))
        }
        val::ValType::F32 => {
            let v: f32 = obj.extract()?;
            Ok(val::Val::F32(v))
        }
        val::ValType::F64 => {
            let v: f64 = obj.extract()?;
            Ok(val::Val::F64(v))
        }
        val::ValType::V128 => {
            let v: u128 = obj.extract()?;
            Ok(val::Val::V128(v))
        }
        val::ValType::Char => {
            let s: String = obj.extract()?;
            let c = s
                .chars()
                .next()
                .ok_or_else(|| PyValueError::new_err("empty string for char"))?;
            if s.len() != c.len_utf8() {
                return Err(PyValueError::new_err("expected a single character"));
            }
            Ok(val::Val::Char(c))
        }
        val::ValType::String => {
            let v: String = obj.extract()?;
            Ok(val::Val::String(v))
        }
        val::ValType::List(elem_ty) => {
            let list = obj.cast::<PyList>()?;
            let items: Vec<val::Val> = list
                .iter()
                .map(|item| val_from_python(elem_ty, &item))
                .collect::<PyResult<_>>()?;
            Ok(val::Val::List(items))
        }
        val::ValType::Record(field_types) => {
            let dict = obj.cast::<PyDict>()?;
            let mut fields = Vec::with_capacity(field_types.len());
            for (name, field_ty) in field_types {
                let value = dict
                    .get_item(name)?
                    .ok_or_else(|| PyValueError::new_err(format!("missing field: {name}")))?;
                fields.push((name.clone(), val_from_python(field_ty, &value)?));
            }
            Ok(val::Val::Record(fields))
        }
        val::ValType::Tuple(item_types) => {
            let tuple = obj.cast::<PyTuple>()?;
            if tuple.len() != item_types.len() {
                return Err(PyValueError::new_err(format!(
                    "expected tuple of length {}, got {}",
                    item_types.len(),
                    tuple.len()
                )));
            }
            let items: Vec<val::Val> = tuple
                .iter()
                .zip(item_types.iter())
                .map(|(item, ty)| val_from_python(ty, &item))
                .collect::<PyResult<_>>()?;
            Ok(val::Val::Tuple(items))
        }
        val::ValType::Variant(cases) => {
            // Expect a dict with "case" and optional "payload"
            let dict = obj.cast::<PyDict>()?;
            let case: String = dict
                .get_item("case")?
                .ok_or_else(|| PyValueError::new_err("variant dict missing 'case' key"))?
                .extract()?;
            let case_type = cases
                .iter()
                .find(|(name, _)| name == &case)
                .ok_or_else(|| PyValueError::new_err(format!("unknown variant case: {case}")))?;
            let payload = match &case_type.1 {
                Some(payload_ty) => {
                    let payload_obj = dict.get_item("payload")?.ok_or_else(|| {
                        PyValueError::new_err("variant case expects payload but none given")
                    })?;
                    Some(Box::new(val_from_python(payload_ty, &payload_obj)?))
                }
                None => None,
            };
            Ok(val::Val::Variant { case, payload })
        }
        val::ValType::Enum(cases) => {
            let case: String = obj.extract()?;
            if !cases.contains(&case) {
                return Err(PyValueError::new_err(format!("unknown enum case: {case}")));
            }
            Ok(val::Val::Enum(case))
        }
        val::ValType::Option(inner_ty) => {
            if obj.is_none() {
                Ok(val::Val::Option(None))
            } else {
                let inner = val_from_python(inner_ty, obj)?;
                Ok(val::Val::Option(Some(Box::new(inner))))
            }
        }
        val::ValType::Result { ok, err } => {
            // Expect a dict with "ok" (bool) and "value"
            let dict = obj.cast::<PyDict>()?;
            let is_ok: bool = dict
                .get_item("ok")?
                .ok_or_else(|| PyValueError::new_err("result dict missing 'ok' key"))?
                .extract()?;
            if is_ok {
                let val = match ok {
                    Some(ok_ty) => {
                        let v = dict
                            .get_item("value")?
                            .ok_or_else(|| PyValueError::new_err("result missing 'value'"))?;
                        if v.is_none() {
                            None
                        } else {
                            Some(Box::new(val_from_python(ok_ty, &v)?))
                        }
                    }
                    None => None,
                };
                Ok(val::Val::Result(Ok(val)))
            } else {
                let val = match err {
                    Some(err_ty) => {
                        let v = dict
                            .get_item("value")?
                            .ok_or_else(|| PyValueError::new_err("result missing 'value'"))?;
                        if v.is_none() {
                            None
                        } else {
                            Some(Box::new(val_from_python(err_ty, &v)?))
                        }
                    }
                    None => None,
                };
                Ok(val::Val::Result(Err(val)))
            }
        }
        val::ValType::Flags(valid) => {
            let list = obj.cast::<PyList>()?;
            let flags: Vec<String> = list
                .iter()
                .map(|item| item.extract::<String>())
                .collect::<PyResult<_>>()?;
            for f in &flags {
                if !valid.contains(f) {
                    return Err(PyValueError::new_err(format!("unknown flag: {f}")));
                }
            }
            Ok(val::Val::Flags(flags))
        }
        val::ValType::Resource(_) => Err(PyTypeError::new_err(
            "resource values are not yet supported",
        )),
    }
}
