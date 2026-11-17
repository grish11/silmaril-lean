//! Run certificate-checking Wasm component acceptors under Wasmtime and record what happened.
//!
//! A suite (JSON) names component artifacts by path (optionally pinned by SHA-256) and lists
//! cases: an export, its positional arguments as JSON, the expected outcome and a class
//! (`positive`, `negative`, `malformed`, `trap`). Arguments are converted to component values
//! through the export's *actual* parameter types, read from the component, so the harness only
//! needs to know the JSON shape of each WIT type it supports. Each case runs in a fresh store and
//! instance.
//!
//! Outcomes are kept apart: `accepted` (the export returned `true`), `rejected` (`false`),
//! `trap` (a Wasm trap, with its code), `error` (instantiation, linking or any other host
//! error) and `unsupported` (a missing export, an unsupported type or argument shape, a result
//! that is not a single `bool`). A case passes only when the observed outcome is the expected
//! one; a missing expectation is reported as `unchecked`, never as a pass.
//!
//! These are observations of one engine on concrete inputs, not proofs: an `accepted` record
//! is evidence that this Wasmtime build returned `true`, not that the input is in any language.

use anyhow::{Context, Result, anyhow, bail};
use clap::Parser;
use serde::{Deserialize, Serialize};
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use wasmtime::component::{Component, Linker, Type, Val};
use wasmtime::{Config, Engine, Store};

/// The Wasmtime version this harness is built against (pinned exactly in `Cargo.toml`).
const WASMTIME_VERSION: &str = "50.0.0";

#[derive(Parser)]
#[command(about = "Run component acceptor suites under Wasmtime")]
struct Cli {
    /// Suite files (JSON).
    #[arg(required = true)]
    suites: Vec<PathBuf>,
    /// Write the JSON report here.
    #[arg(long)]
    out: Option<PathBuf>,
}

#[derive(Deserialize)]
struct Suite {
    suite: String,
    #[serde(default)]
    description: String,
    artifacts: BTreeMap<String, ArtifactSpec>,
    cases: Vec<Case>,
}

#[derive(Deserialize)]
struct ArtifactSpec {
    /// Path relative to the suite file.
    path: PathBuf,
    /// Expected SHA-256 (hex); a mismatch is an error for every case of the artifact.
    #[serde(default)]
    sha256: Option<String>,
    /// What the artifact is claimed to be (for example the Lean value it encodes).
    #[serde(default)]
    source: String,
}

#[derive(Deserialize, Clone)]
struct Case {
    name: String,
    artifact: String,
    export: String,
    #[serde(default)]
    class: String,
    args: Vec<Json>,
    #[serde(default)]
    expect: Option<Outcome>,
    #[serde(default)]
    note: String,
}

#[derive(Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "lowercase")]
enum Outcome {
    Accepted,
    Rejected,
    Trap,
    Error,
    Unsupported,
}

#[derive(Serialize)]
struct Observed {
    outcome: Outcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    detail: Option<String>,
}

#[derive(Serialize)]
struct ArtifactRecord {
    id: String,
    path: String,
    source: String,
    bytes: usize,
    sha256: String,
    blake3: String,
    pinned_sha256_ok: Option<bool>,
}

#[derive(Serialize)]
struct CaseRecord {
    suite: String,
    name: String,
    artifact: String,
    sha256: String,
    export: String,
    params: Vec<String>,
    class: String,
    args: Vec<Json>,
    expected: Option<Outcome>,
    observed: Observed,
    /// `pass`, `fail` or `unchecked` (no expectation given).
    verdict: String,
    note: String,
}

#[derive(Serialize)]
struct EngineRecord {
    name: &'static str,
    version: &'static str,
    config: BTreeMap<&'static str, Json>,
}

#[derive(Serialize)]
struct Report {
    kind: &'static str,
    evidence: &'static str,
    command: Vec<String>,
    engine: EngineRecord,
    artifacts: Vec<ArtifactRecord>,
    cases: Vec<CaseRecord>,
    summary: BTreeMap<String, usize>,
}

fn engine_config() -> (Config, BTreeMap<&'static str, Json>) {
    let mut config = Config::new();
    config.wasm_component_model(true);
    config.cranelift_nan_canonicalization(false);
    let mut record = BTreeMap::new();
    record.insert("component_model", Json::Bool(true));
    record.insert("compiler", Json::from("cranelift"));
    record.insert("nan_canonicalization", Json::Bool(false));
    record.insert("fuel", Json::Bool(false));
    record.insert("linker", Json::from("empty (no imports provided)"));
    record.insert("instance", Json::from("fresh store and instance per case"));
    (config, record)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A JSON value as a component value of type `ty`.
fn to_val(ty: &Type, j: &Json) -> Result<Val, String> {
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
    match ty {
        Type::Bool => j
            .as_bool()
            .map(Val::Bool)
            .ok_or_else(|| format!("expected bool, got {j}")),
        Type::S32 => int(i32::MIN.into(), i32::MAX.into()).map(|n| Val::S32(n as i32)),
        Type::U32 => int(0, u32::MAX.into()).map(|n| Val::U32(n as u32)),
        Type::S64 => int(i64::MIN.into(), i64::MAX.into()).map(|n| Val::S64(n as i64)),
        Type::U64 => int(0, u64::MAX.into()).map(|n| Val::U64(n as u64)),
        Type::List(l) => {
            let elem = l.ty();
            // `{"$repeat": v, "count": n}`: the list of `n` copies of `v` (large inputs).
            if let Some(obj) = j.as_object().filter(|o| o.contains_key("$repeat")) {
                let n = obj
                    .get("count")
                    .and_then(Json::as_u64)
                    .ok_or_else(|| format!("bad $repeat {j}"))?;
                let v = to_val(&elem, &obj["$repeat"])?;
                return Ok(Val::List(vec![v; n as usize]));
            }
            let xs = j
                .as_array()
                .ok_or_else(|| format!("expected a list, got {j}"))?;
            xs.iter()
                .map(|x| to_val(&elem, x))
                .collect::<Result<Vec<_>, _>>()
                .map(Val::List)
        }
        Type::Tuple(t) => {
            let xs = j
                .as_array()
                .ok_or_else(|| format!("expected a tuple array, got {j}"))?;
            let tys: Vec<Type> = t.types().collect();
            if xs.len() != tys.len() {
                return Err(format!("expected a {}-tuple, got {j}", tys.len()));
            }
            tys.iter()
                .zip(xs)
                .map(|(t, x)| to_val(t, x))
                .collect::<Result<Vec<_>, _>>()
                .map(Val::Tuple)
        }
        Type::Record(r) => {
            let obj = j
                .as_object()
                .ok_or_else(|| format!("expected a record object, got {j}"))?;
            let mut fields = Vec::new();
            for f in r.fields() {
                let v = obj
                    .get(f.name)
                    .ok_or_else(|| format!("missing record field {}", f.name))?;
                fields.push((f.name.to_string(), to_val(&f.ty, v)?));
            }
            if obj.len() != fields.len() {
                return Err(format!("unexpected record fields in {j}"));
            }
            Ok(Val::Record(fields))
        }
        other => Err(format!("unsupported parameter type {other:?}")),
    }
}

fn type_name(ty: &Type) -> String {
    match ty {
        Type::Bool => "bool".into(),
        Type::S32 => "s32".into(),
        Type::U32 => "u32".into(),
        Type::S64 => "s64".into(),
        Type::U64 => "u64".into(),
        Type::List(l) => format!("list<{}>", type_name(&l.ty())),
        Type::Tuple(t) => format!(
            "tuple<{}>",
            t.types()
                .map(|t| type_name(&t))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Type::Record(r) => format!(
            "record {{ {} }}",
            r.fields()
                .map(|f| format!("{}: {}", f.name, type_name(&f.ty)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        other => format!("{other:?}"),
    }
}

/// Run one case on `bytes`: returns the parameter signature and the observation.
fn run_case(engine: &Engine, component: &Component, case: &Case) -> (Vec<String>, Observed) {
    let obs = |outcome, detail: String| Observed {
        outcome,
        detail: Some(detail),
    };
    let linker: Linker<()> = Linker::new(engine);
    let mut store = Store::new(engine, ());
    let instance = match linker.instantiate(&mut store, component) {
        Ok(i) => i,
        Err(e) => return (vec![], obs(Outcome::Error, format!("instantiation: {e:#}"))),
    };
    let Some(func) = instance.get_func(&mut store, &case.export) else {
        return (
            vec![],
            obs(Outcome::Unsupported, format!("no export {}", case.export)),
        );
    };
    let fty = func.ty(&store);
    let params: Vec<(String, Type)> = fty.params().map(|(n, t)| (n.to_string(), t)).collect();
    let sig = params
        .iter()
        .map(|(n, t)| format!("{n}: {}", type_name(t)))
        .collect::<Vec<_>>();
    let results: Vec<Type> = fty.results().collect();
    if !matches!(results.as_slice(), [Type::Bool]) {
        return (
            sig,
            obs(
                Outcome::Unsupported,
                "the export does not return one bool".into(),
            ),
        );
    }
    if params.len() != case.args.len() {
        return (
            sig,
            obs(
                Outcome::Unsupported,
                format!(
                    "{} arguments for {} parameters",
                    case.args.len(),
                    params.len()
                ),
            ),
        );
    }
    let mut args = Vec::new();
    for ((_, t), a) in params.iter().zip(&case.args) {
        match to_val(t, a) {
            Ok(v) => args.push(v),
            Err(e) => return (sig, obs(Outcome::Unsupported, e)),
        }
    }
    let mut out = [Val::Bool(false)];
    match func.call(&mut store, &args, &mut out) {
        Ok(()) => match out[0] {
            Val::Bool(true) => (
                sig,
                Observed {
                    outcome: Outcome::Accepted,
                    detail: None,
                },
            ),
            Val::Bool(false) => (
                sig,
                Observed {
                    outcome: Outcome::Rejected,
                    detail: None,
                },
            ),
            ref v => (
                sig,
                obs(Outcome::Unsupported, format!("non-bool result {v:?}")),
            ),
        },
        Err(e) => match e.downcast_ref::<wasmtime::Trap>() {
            Some(t) => (sig, obs(Outcome::Trap, format!("{t}"))),
            None => (sig, obs(Outcome::Error, format!("{e:#}"))),
        },
    }
}

fn load_suite(path: &Path) -> Result<Suite> {
    let text =
        std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    serde_json::from_str(&text).with_context(|| format!("parsing {}", path.display()))
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let (config, config_record) = engine_config();
    let engine = Engine::new(&config).map_err(|e| anyhow!("creating the engine: {e:#}"))?;
    let mut report = Report {
        kind: "silmaril.wasm-acceptor-harness.report/v1",
        evidence: "runtime observations of one engine on concrete inputs; not a proof",
        command: std::env::args().collect(),
        engine: EngineRecord {
            name: "wasmtime",
            version: WASMTIME_VERSION,
            config: config_record,
        },
        artifacts: vec![],
        cases: vec![],
        summary: BTreeMap::new(),
    };
    for suite_path in &cli.suites {
        let suite = load_suite(suite_path)?;
        let base = suite_path.parent().unwrap_or(Path::new("."));
        let mut loaded: BTreeMap<String, (String, Result<Component, String>)> = BTreeMap::new();
        for (id, spec) in &suite.artifacts {
            let path = base.join(&spec.path);
            let bytes = std::fs::read(&path)
                .with_context(|| format!("reading artifact {}", path.display()))?;
            let sha = hex(&Sha256::digest(&bytes));
            let pinned_ok = spec.sha256.as_ref().map(|s| s.eq_ignore_ascii_case(&sha));
            let component = match pinned_ok {
                Some(false) => Err(format!(
                    "SHA-256 mismatch: pinned {}, file {sha}",
                    spec.sha256.as_deref().unwrap_or("")
                )),
                _ => {
                    Component::from_binary(&engine, &bytes).map_err(|e| format!("compiling: {e:#}"))
                }
            };
            report.artifacts.push(ArtifactRecord {
                id: format!("{}/{id}", suite.suite),
                path: spec.path.display().to_string(),
                source: spec.source.clone(),
                bytes: bytes.len(),
                sha256: sha.clone(),
                blake3: blake3::hash(&bytes).to_hex().to_string(),
                pinned_sha256_ok: pinned_ok,
            });
            loaded.insert(id.clone(), (sha, component));
        }
        for case in &suite.cases {
            let Some((sha, component)) = loaded.get(&case.artifact) else {
                bail!(
                    "{}: case {} names unknown artifact {}",
                    suite.suite,
                    case.name,
                    case.artifact
                );
            };
            let (params, observed) = match component {
                Ok(c) => run_case(&engine, c, case),
                Err(e) => (
                    vec![],
                    Observed {
                        outcome: Outcome::Error,
                        detail: Some(e.clone()),
                    },
                ),
            };
            let verdict = match case.expect {
                None => "unchecked",
                Some(x) if x == observed.outcome => "pass",
                Some(_) => "fail",
            };
            *report.summary.entry(verdict.to_string()).or_default() += 1;
            println!(
                "{verdict:9} {}/{}: {} -> {:?}{}",
                suite.suite,
                case.name,
                case.export,
                observed.outcome,
                observed
                    .detail
                    .as_ref()
                    .map(|d| format!(" ({d})"))
                    .unwrap_or_default()
            );
            report.cases.push(CaseRecord {
                suite: suite.suite.clone(),
                name: case.name.clone(),
                artifact: case.artifact.clone(),
                sha256: sha.clone(),
                export: case.export.clone(),
                params,
                class: case.class.clone(),
                args: case.args.clone(),
                expected: case.expect,
                observed,
                verdict: verdict.to_string(),
                note: case.note.clone(),
            });
        }
        let _ = &suite.description;
    }
    if let Some(out) = &cli.out {
        std::fs::write(out, serde_json::to_string_pretty(&report)? + "\n")?;
    }
    let fails = report.summary.get("fail").copied().unwrap_or(0);
    println!("summary: {:?}", report.summary);
    if fails > 0 {
        return Err(anyhow!("{fails} case(s) did not match their expectation"));
    }
    Ok(())
}
