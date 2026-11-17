//! Component values from JSON, by the export's actual parameter types.
//!
//! [`Ty`] is a plain description of a component value type, read from a component's
//! [`wasmtime::component::Type`] by [`Ty::of`]; [`to_val`] converts a JSON value to the
//! [`Val`] of a type, and [`Ty::name`] prints the type in WIT notation (the signature in the
//! report). The JSON shape of each type (documented in the harness README and in
//! `docs/schemas/wasm-acceptor-suite.v1.schema.json`):
//!
//! | type | JSON |
//! |---|---|
//! | `bool` | `true` / `false` |
//! | `s8` … `u64` | an integer number in range |
//! | `f32`, `f64` | a number, or `"nan"`, `"inf"`, `"-inf"` |
//! | `char` | a string of exactly one Unicode scalar value |
//! | `string` | a string |
//! | `list<T>` | an array, or `{"$repeat": v, "count": n}` (`n` copies of `v`) |
//! | `tuple<…>` | an array of exactly that length |
//! | `record` | an object with exactly the record's fields |
//! | `variant` | `{"case": "name"}`, or `{"case": "name", "value": v}` for a case with payload |
//! | `enum` | the case name as a string |
//! | `option<T>` | `null` (none) or `{"some": v}` |
//! | `result<T, E>` | `{"ok": v}` or `{"err": v}`; `v` is `null` on a side without a type |
//! | `flags` | an array of distinct flag names |
//!
//! Every other type (resources, `map`, fixed-length lists, `future`, `stream`, `error-context`)
//! is [`Ty::Unsupported`]: converting to it is an error, which the harness records as the
//! outcome `unsupported`.

use serde_json::Value as Json;
use wasmtime::component::{Type, Val};

/// A component value type, as far as the harness converts JSON to it.
#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
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
    Char,
    String,
    List(Box<Ty>),
    Tuple(Vec<Ty>),
    Record(Vec<(String, Ty)>),
    Variant(Vec<(String, Option<Ty>)>),
    Enum(Vec<String>),
    Option(Box<Ty>),
    Result(Option<Box<Ty>>, Option<Box<Ty>>),
    Flags(Vec<String>),
    /// A type the harness has no JSON shape for, by its WIT-like name.
    Unsupported(String),
}

impl Ty {
    /// The description of a component's type.
    pub fn of(ty: &Type) -> Ty {
        let of_opt = |t: Option<Type>| t.map(|t| Box::new(Ty::of(&t)));
        match ty {
            Type::Bool => Ty::Bool,
            Type::S8 => Ty::S8,
            Type::U8 => Ty::U8,
            Type::S16 => Ty::S16,
            Type::U16 => Ty::U16,
            Type::S32 => Ty::S32,
            Type::U32 => Ty::U32,
            Type::S64 => Ty::S64,
            Type::U64 => Ty::U64,
            Type::Float32 => Ty::F32,
            Type::Float64 => Ty::F64,
            Type::Char => Ty::Char,
            Type::String => Ty::String,
            Type::List(l) => Ty::List(Box::new(Ty::of(&l.ty()))),
            Type::Tuple(t) => Ty::Tuple(t.types().map(|t| Ty::of(&t)).collect()),
            Type::Record(r) => Ty::Record(
                r.fields()
                    .map(|f| (f.name.to_string(), Ty::of(&f.ty)))
                    .collect(),
            ),
            Type::Variant(v) => Ty::Variant(
                v.cases()
                    .map(|c| (c.name.to_string(), c.ty.as_ref().map(Ty::of)))
                    .collect(),
            ),
            Type::Enum(e) => Ty::Enum(e.names().map(str::to_string).collect()),
            Type::Option(o) => Ty::Option(Box::new(Ty::of(&o.ty()))),
            Type::Result(r) => Ty::Result(of_opt(r.ok()), of_opt(r.err())),
            Type::Flags(f) => Ty::Flags(f.names().map(str::to_string).collect()),
            Type::Map(_) => Ty::Unsupported("map".into()),
            Type::Own(_) => Ty::Unsupported("own<resource>".into()),
            Type::Borrow(_) => Ty::Unsupported("borrow<resource>".into()),
            Type::Future(_) => Ty::Unsupported("future".into()),
            Type::Stream(_) => Ty::Unsupported("stream".into()),
            Type::ErrorContext => Ty::Unsupported("error-context".into()),
            Type::FixedLengthList(_) => Ty::Unsupported("fixed-length list".into()),
        }
    }

    /// The type in WIT notation (structural: records, variants, enums and flags are spelled out).
    pub fn name(&self) -> String {
        let join = |xs: Vec<String>| xs.join(", ");
        match self {
            Ty::Bool => "bool".into(),
            Ty::S8 => "s8".into(),
            Ty::U8 => "u8".into(),
            Ty::S16 => "s16".into(),
            Ty::U16 => "u16".into(),
            Ty::S32 => "s32".into(),
            Ty::U32 => "u32".into(),
            Ty::S64 => "s64".into(),
            Ty::U64 => "u64".into(),
            Ty::F32 => "f32".into(),
            Ty::F64 => "f64".into(),
            Ty::Char => "char".into(),
            Ty::String => "string".into(),
            Ty::List(t) => format!("list<{}>", t.name()),
            Ty::Tuple(ts) => format!("tuple<{}>", join(ts.iter().map(Ty::name).collect())),
            Ty::Record(fs) => format!(
                "record {{ {} }}",
                join(
                    fs.iter()
                        .map(|(n, t)| format!("{n}: {}", t.name()))
                        .collect()
                )
            ),
            Ty::Variant(cs) => format!(
                "variant {{ {} }}",
                join(
                    cs.iter()
                        .map(|(n, t)| match t {
                            Some(t) => format!("{n}({})", t.name()),
                            None => n.clone(),
                        })
                        .collect()
                )
            ),
            Ty::Enum(ns) => format!("enum {{ {} }}", ns.join(", ")),
            Ty::Option(t) => format!("option<{}>", t.name()),
            Ty::Result(ok, err) => {
                let side = |t: &Option<Box<Ty>>| t.as_ref().map(|t| t.name());
                match (side(ok), side(err)) {
                    (None, None) => "result".into(),
                    (Some(o), None) => format!("result<{o}>"),
                    (None, Some(e)) => format!("result<_, {e}>"),
                    (Some(o), Some(e)) => format!("result<{o}, {e}>"),
                }
            }
            Ty::Flags(ns) => format!("flags {{ {} }}", ns.join(", ")),
            Ty::Unsupported(n) => n.clone(),
        }
    }
}

/// A JSON value as a component value of type `ty`; an error names what did not fit.
pub fn to_val(ty: &Ty, j: &Json) -> Result<Val, String> {
    let int = |lo: i128, hi: i128| -> Result<i128, String> {
        let n = j
            .as_i64()
            .map(i128::from)
            .or_else(|| j.as_u64().map(i128::from));
        match n {
            Some(n) if lo <= n && n <= hi => Ok(n),
            _ => Err(format!("expected an integer in [{lo}, {hi}], got {j}")),
        }
    };
    let obj = |what: &str| {
        j.as_object()
            .ok_or_else(|| format!("expected {what} object, got {j}"))
    };
    // The only key of a one-key object, and its value.
    let single = |what: &str| -> Result<(&str, &Json), String> {
        let o = obj(what)?;
        match o.iter().next() {
            Some((k, v)) if o.len() == 1 => Ok((k.as_str(), v)),
            _ => Err(format!("expected {what} object with one key, got {j}")),
        }
    };
    match ty {
        Ty::Bool => j
            .as_bool()
            .map(Val::Bool)
            .ok_or_else(|| format!("expected bool, got {j}")),
        Ty::S8 => int(i8::MIN.into(), i8::MAX.into()).map(|n| Val::S8(n as i8)),
        Ty::U8 => int(0, u8::MAX.into()).map(|n| Val::U8(n as u8)),
        Ty::S16 => int(i16::MIN.into(), i16::MAX.into()).map(|n| Val::S16(n as i16)),
        Ty::U16 => int(0, u16::MAX.into()).map(|n| Val::U16(n as u16)),
        Ty::S32 => int(i32::MIN.into(), i32::MAX.into()).map(|n| Val::S32(n as i32)),
        Ty::U32 => int(0, u32::MAX.into()).map(|n| Val::U32(n as u32)),
        Ty::S64 => int(i64::MIN.into(), i64::MAX.into()).map(|n| Val::S64(n as i64)),
        Ty::U64 => int(0, u64::MAX.into()).map(|n| Val::U64(n as u64)),
        Ty::F32 => {
            let x = float(j)?;
            if x.is_finite() && x.abs() > f64::from(f32::MAX) {
                return Err(format!("{j} is out of the range of f32"));
            }
            Ok(Val::Float32(x as f32))
        }
        Ty::F64 => float(j).map(Val::Float64),
        Ty::Char => {
            let s = j
                .as_str()
                .ok_or_else(|| format!("expected a one-character string, got {j}"))?;
            let mut cs = s.chars();
            match (cs.next(), cs.next()) {
                (Some(c), None) => Ok(Val::Char(c)),
                _ => Err(format!("expected exactly one character, got {j}")),
            }
        }
        Ty::String => j
            .as_str()
            .map(|s| Val::String(s.to_string()))
            .ok_or_else(|| format!("expected a string, got {j}")),
        Ty::List(elem) => {
            if let Some(o) = j.as_object().filter(|o| o.contains_key("$repeat")) {
                let n = o
                    .get("count")
                    .and_then(Json::as_u64)
                    .filter(|_| o.len() == 2)
                    .ok_or_else(|| format!("bad $repeat {j}"))?;
                let v = to_val(elem, &o["$repeat"])?;
                return Ok(Val::List(vec![v; n as usize]));
            }
            let xs = j
                .as_array()
                .ok_or_else(|| format!("expected a list, got {j}"))?;
            xs.iter()
                .map(|x| to_val(elem, x))
                .collect::<Result<Vec<_>, _>>()
                .map(Val::List)
        }
        Ty::Tuple(tys) => {
            let xs = j
                .as_array()
                .ok_or_else(|| format!("expected a tuple array, got {j}"))?;
            if xs.len() != tys.len() {
                return Err(format!("expected a {}-tuple, got {j}", tys.len()));
            }
            tys.iter()
                .zip(xs)
                .map(|(t, x)| to_val(t, x))
                .collect::<Result<Vec<_>, _>>()
                .map(Val::Tuple)
        }
        Ty::Record(fs) => {
            let o = obj("a record")?;
            let mut fields = Vec::new();
            for (name, t) in fs {
                let v = o
                    .get(name)
                    .ok_or_else(|| format!("missing record field {name}"))?;
                fields.push((name.clone(), to_val(t, v)?));
            }
            if o.len() != fields.len() {
                return Err(format!("unexpected record fields in {j}"));
            }
            Ok(Val::Record(fields))
        }
        Ty::Variant(cs) => {
            let o = obj("a variant")?;
            let name = o
                .get("case")
                .and_then(Json::as_str)
                .ok_or_else(|| format!("expected {{\"case\": name, ...}}, got {j}"))?;
            let (_, payload) = cs
                .iter()
                .find(|(n, _)| n == name)
                .ok_or_else(|| format!("no variant case {name}"))?;
            let extra = o.keys().any(|k| k != "case" && k != "value");
            if extra {
                return Err(format!("unexpected keys in variant {j}"));
            }
            let v = match (payload, o.get("value")) {
                (Some(t), Some(v)) => Some(Box::new(to_val(t, v)?)),
                (Some(_), None) => return Err(format!("variant case {name} needs a value")),
                (None, None) => None,
                (None, Some(_)) => return Err(format!("variant case {name} has no payload")),
            };
            Ok(Val::Variant(name.to_string(), v))
        }
        Ty::Enum(ns) => {
            let s = j
                .as_str()
                .ok_or_else(|| format!("expected an enum case name, got {j}"))?;
            if ns.iter().any(|n| n == s) {
                Ok(Val::Enum(s.to_string()))
            } else {
                Err(format!("no enum case {s}"))
            }
        }
        Ty::Option(t) => {
            if j.is_null() {
                return Ok(Val::Option(None));
            }
            match single("an option (null or {\"some\": v})")? {
                ("some", v) => Ok(Val::Option(Some(Box::new(to_val(t, v)?)))),
                _ => Err(format!("expected null or {{\"some\": v}}, got {j}")),
            }
        }
        Ty::Result(ok, err) => {
            let side = |t: &Option<Box<Ty>>, v: &Json| -> Result<Option<Box<Val>>, String> {
                match t {
                    Some(t) => Ok(Some(Box::new(to_val(t, v)?))),
                    None if v.is_null() => Ok(None),
                    None => Err(format!(
                        "this result side has no payload: expected null, got {v}"
                    )),
                }
            };
            match single("a result ({\"ok\": v} or {\"err\": v})")? {
                ("ok", v) => Ok(Val::Result(Ok(side(ok, v)?))),
                ("err", v) => Ok(Val::Result(Err(side(err, v)?))),
                _ => Err(format!("expected {{\"ok\": v}} or {{\"err\": v}}, got {j}")),
            }
        }
        Ty::Flags(ns) => {
            let xs = j
                .as_array()
                .ok_or_else(|| format!("expected an array of flag names, got {j}"))?;
            let mut out: Vec<String> = Vec::new();
            for x in xs {
                let s = x
                    .as_str()
                    .ok_or_else(|| format!("expected a flag name, got {x}"))?;
                if !ns.iter().any(|n| n == s) {
                    return Err(format!("no flag {s}"));
                }
                if out.iter().any(|o| o == s) {
                    return Err(format!("flag {s} given twice"));
                }
                out.push(s.to_string());
            }
            Ok(Val::Flags(out))
        }
        Ty::Unsupported(n) => Err(format!("unsupported parameter type {n}")),
    }
}

/// A float: a JSON number, or `"nan"`, `"inf"`, `"-inf"`.
fn float(j: &Json) -> Result<f64, String> {
    match j {
        Json::Number(n) => n.as_f64().ok_or_else(|| format!("bad number {j}")),
        Json::String(s) => match s.as_str() {
            "nan" => Ok(f64::NAN),
            "inf" => Ok(f64::INFINITY),
            "-inf" => Ok(f64::NEG_INFINITY),
            _ => Err(format!(
                "expected a number, \"nan\", \"inf\" or \"-inf\", got {j}"
            )),
        },
        _ => Err(format!("expected a number, got {j}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn ok(ty: &Ty, j: Json) -> Val {
        to_val(ty, &j).unwrap_or_else(|e| panic!("{} from {j}: {e}", ty.name()))
    }
    fn bad(ty: &Ty, j: Json) -> String {
        match to_val(ty, &j) {
            Ok(v) => panic!("{} from {j} gave {v:?}", ty.name()),
            Err(e) => e,
        }
    }

    #[test]
    fn integers_by_range() {
        assert_eq!(ok(&Ty::S8, json!(-128)), Val::S8(-128));
        bad(&Ty::S8, json!(128));
        assert_eq!(ok(&Ty::U8, json!(255)), Val::U8(255));
        bad(&Ty::U8, json!(-1));
        assert_eq!(ok(&Ty::S16, json!(-32768)), Val::S16(-32768));
        bad(&Ty::U16, json!(65536));
        assert_eq!(ok(&Ty::S32, json!(i32::MIN)), Val::S32(i32::MIN));
        bad(&Ty::U32, json!(1u64 << 32));
        assert_eq!(ok(&Ty::U64, json!(u64::MAX)), Val::U64(u64::MAX));
        assert_eq!(ok(&Ty::S64, json!(i64::MIN)), Val::S64(i64::MIN));
        bad(&Ty::S64, json!(u64::MAX));
        bad(&Ty::U32, json!(1.0));
        bad(&Ty::U32, json!("1"));
        assert_eq!(ok(&Ty::Bool, json!(true)), Val::Bool(true));
        bad(&Ty::Bool, json!(1));
    }

    #[test]
    fn floats_chars_strings() {
        assert_eq!(ok(&Ty::F64, json!(1.5)), Val::Float64(1.5));
        assert_eq!(ok(&Ty::F64, json!(-3)), Val::Float64(-3.0));
        assert_eq!(ok(&Ty::F32, json!(0.25)), Val::Float32(0.25));
        assert_eq!(ok(&Ty::F32, json!("-inf")), Val::Float32(f32::NEG_INFINITY));
        assert!(matches!(ok(&Ty::F64, json!("nan")), Val::Float64(x) if x.is_nan()));
        bad(&Ty::F32, json!(1e39));
        bad(&Ty::F64, json!("1.0"));
        assert_eq!(ok(&Ty::Char, json!("λ")), Val::Char('λ'));
        bad(&Ty::Char, json!("ab"));
        bad(&Ty::Char, json!(""));
        assert_eq!(
            ok(&Ty::String, json!("a\u{0}b")),
            Val::String("a\u{0}b".into())
        );
        bad(&Ty::String, json!(["a"]));
    }

    #[test]
    fn lists_tuples_records() {
        let l = Ty::List(Box::new(Ty::S32));
        assert_eq!(
            ok(&l, json!([1, -2])),
            Val::List(vec![Val::S32(1), Val::S32(-2)])
        );
        assert_eq!(
            ok(&l, json!({"$repeat": 7, "count": 3})),
            Val::List(vec![Val::S32(7); 3])
        );
        bad(&l, json!({"$repeat": 7}));
        bad(&l, json!({"$repeat": 7, "count": 3, "x": 0}));
        bad(&l, json!([1, "2"]));
        let t = Ty::Tuple(vec![Ty::U32, Ty::S64]);
        assert_eq!(
            ok(&t, json!([0, -1])),
            Val::Tuple(vec![Val::U32(0), Val::S64(-1)])
        );
        bad(&t, json!([0]));
        let r = Ty::Record(vec![("a".into(), Ty::U8), ("b".into(), Ty::Bool)]);
        // Fields in the record's order, whatever the JSON order.
        assert_eq!(
            ok(&r, json!({"b": false, "a": 1})),
            Val::Record(vec![
                ("a".into(), Val::U8(1)),
                ("b".into(), Val::Bool(false))
            ])
        );
        bad(&r, json!({"a": 1}));
        bad(&r, json!({"a": 1, "b": true, "c": 0}));
    }

    #[test]
    fn variants_enums_options_results_flags() {
        let v = Ty::Variant(vec![("none".into(), None), ("num".into(), Some(Ty::U16))]);
        assert_eq!(
            ok(&v, json!({"case": "none"})),
            Val::Variant("none".into(), None)
        );
        assert_eq!(
            ok(&v, json!({"case": "num", "value": 9})),
            Val::Variant("num".into(), Some(Box::new(Val::U16(9))))
        );
        bad(&v, json!({"case": "num"}));
        bad(&v, json!({"case": "none", "value": 1}));
        bad(&v, json!({"case": "other"}));
        bad(&v, json!("none"));
        let e = Ty::Enum(vec!["lt".into(), "le".into()]);
        assert_eq!(ok(&e, json!("le")), Val::Enum("le".into()));
        bad(&e, json!("eq"));
        let o = Ty::Option(Box::new(Ty::Option(Box::new(Ty::S8))));
        assert_eq!(ok(&o, json!(null)), Val::Option(None));
        assert_eq!(
            ok(&o, json!({"some": null})),
            Val::Option(Some(Box::new(Val::Option(None))))
        );
        assert_eq!(
            ok(&o, json!({"some": {"some": -1}})),
            Val::Option(Some(Box::new(Val::Option(Some(Box::new(Val::S8(-1)))))))
        );
        bad(&o, json!(1));
        bad(&o, json!({"some": 1, "x": 2}));
        let r = Ty::Result(Some(Box::new(Ty::String)), None);
        assert_eq!(
            ok(&r, json!({"ok": "x"})),
            Val::Result(Ok(Some(Box::new(Val::String("x".into())))))
        );
        assert_eq!(ok(&r, json!({"err": null})), Val::Result(Err(None)));
        bad(&r, json!({"err": 1}));
        bad(&r, json!({"ok": "x", "err": null}));
        assert_eq!(Ty::Result(None, None).name(), "result");
        let f = Ty::Flags(vec!["r".into(), "w".into()]);
        assert_eq!(ok(&f, json!(["w"])), Val::Flags(vec!["w".into()]));
        bad(&f, json!(["w", "w"]));
        bad(&f, json!(["x"]));
        bad(&Ty::Unsupported("own<resource>".into()), json!(0));
    }

    #[test]
    fn names() {
        let t = Ty::List(Box::new(Ty::Record(vec![
            (
                "coeffs".into(),
                Ty::List(Box::new(Ty::Tuple(vec![Ty::U32, Ty::S64]))),
            ),
            ("bound".into(), Ty::S64),
        ])));
        // The spelling of the committed report's signatures.
        assert_eq!(
            t.name(),
            "list<record { coeffs: list<tuple<u32, s64>>, bound: s64 }>"
        );
        let r = Ty::Result(None, Some(Box::new(Ty::Enum(vec!["a".into(), "b".into()]))));
        assert_eq!(r.name(), "result<_, enum { a, b }>");
        let v = Ty::Variant(vec![("x".into(), None), ("y".into(), Some(Ty::F32))]);
        assert_eq!(v.name(), "variant { x, y(f32) }");
    }
}
