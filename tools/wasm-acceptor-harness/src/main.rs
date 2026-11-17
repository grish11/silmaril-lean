//! Run certificate-checking Wasm component acceptors under Wasmtime and record what happened.
//!
//! A suite (JSON, schema `docs/schemas/wasm-acceptor-suite.v1.schema.json`) names component
//! artifacts by path, pinned by SHA-256, optionally with the Lean claims made about exactly
//! those bytes, and lists cases: an export, its positional arguments as JSON, the expected
//! outcome (and optionally a substring of the trap or error detail) and a class (`positive`,
//! `negative`, `malformed`, …). Arguments are converted to component values through the
//! export's *actual* parameter types, read from the component (`value.rs`), so adding a checker
//! means adding a suite file, not code. Each case runs in a fresh store and instance.
//!
//! Outcomes are kept apart: `accepted` (the export returned `true`), `rejected` (`false`),
//! `trap` (a Wasm trap, with its code), `error` (instantiation, linking or any other host
//! error) and `unsupported` (a missing export, an unsupported type or argument shape, a result
//! that is not a single `bool`). A case passes only when the observed outcome is the expected
//! one (and its detail contains `expect_detail`, when given); a missing expectation is reported
//! as `unchecked`, never as a pass.
//!
//! These are observations of one engine on concrete inputs, not proofs: an `accepted` record
//! is evidence that this Wasmtime build returned `true`, not that the input is in any language.
//! The claims are copied from the suite into the report, for the explorer to show apart from
//! the observations; the harness does not check them (the Lean library states them).

mod value;

use anyhow::{Context, Result, anyhow, bail};
use clap::Parser;
use serde::{Deserialize, Serialize};
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use value::{Ty, to_val};
use wasmtime::component::{Component, Linker, Val};
use wasmtime::{Config, Engine, Store};

/// The Wasmtime version this harness is built against (pinned exactly in `Cargo.toml`).
const WASMTIME_VERSION: &str = "50.0.0";
/// The report's kind. v2 added `suites`, per-artifact `claims` and per-case `expected_detail`.
const REPORT_KIND: &str = "silmaril.wasm-acceptor-harness.report/v2";

#[derive(Parser)]
#[command(about = "Run component acceptor suites under Wasmtime")]
struct Cli {
    /// Suite files (JSON).
    #[arg(required = true)]
    suites: Vec<PathBuf>,
    /// Write the JSON report here.
    #[arg(long)]
    out: Option<PathBuf>,
    /// Run only the suites whose name contains this text (repeatable: any of them).
    #[arg(long = "suite-filter", value_name = "TEXT")]
    suite_filter: Vec<String>,
    /// Run only the cases with this name (repeatable: any of them).
    #[arg(long = "case", value_name = "NAME")]
    case: Vec<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Suite {
    #[serde(rename = "$schema", default)]
    _schema: Option<String>,
    suite: String,
    #[serde(default)]
    description: String,
    artifacts: BTreeMap<String, ArtifactSpec>,
    cases: Vec<Case>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ArtifactSpec {
    /// Path relative to the suite file.
    path: PathBuf,
    /// Expected SHA-256 (hex); a mismatch is an error for every case of the artifact.
    #[serde(default)]
    sha256: Option<String>,
    /// What the artifact is claimed to be (for example the Lean value it encodes).
    #[serde(default)]
    source: String,
    /// What the Lean library states about exactly these bytes (needs `sha256`).
    #[serde(default)]
    claims: Vec<Claim>,
}

/// How far a claim reaches.
#[derive(Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
#[serde(rename_all = "kebab-case")]
enum ClaimLevel {
    /// About the component: every reference Component Model reading of the bytes.
    Component,
    /// About the core module inside it only (the canonical ABI wrapping is not covered).
    CoreModule,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct Claim {
    /// The kind of claim as shown, e.g. `component-level soundness (kernel-checked)`.
    kind: String,
    level: ClaimLevel,
    /// The name the bytes are registered under in `silmaril/artifacts.toml`, if any.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    registry_name: Option<String>,
    /// The Lean value the bytes are (by regeneration), e.g. `Silmaril.Wasm.Examples.SatAccept.bytes`.
    value: String,
    /// What the theorems cover and what they leave out.
    scope: String,
    theorems: Vec<Theorem>,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct Theorem {
    decl: String,
    module: String,
    /// One line: what the theorem states.
    states: String,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct Case {
    name: String,
    artifact: String,
    export: String,
    #[serde(default)]
    class: String,
    args: Vec<Json>,
    #[serde(default)]
    expect: Option<Outcome>,
    /// A substring the observed detail must contain (traps and errors).
    #[serde(default)]
    expect_detail: Option<String>,
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

#[derive(Serialize, Debug)]
struct Observed {
    outcome: Outcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    detail: Option<String>,
}

#[derive(Serialize)]
struct SuiteRecord {
    suite: String,
    description: String,
}

#[derive(Serialize)]
struct ClaimRecord {
    /// The SHA-256 the claim was made for (the artifact's pin).
    sha256: String,
    #[serde(flatten)]
    claim: Claim,
}

#[derive(Serialize)]
struct ArtifactRecord {
    id: String,
    path: String,
    source: String,
    bytes: usize,
    sha256: String,
    blake3: String,
    cid: String,
    pinned_sha256_ok: Option<bool>,
    /// The suite's claims, only when the file has the pinned SHA-256.
    claims: Vec<ClaimRecord>,
    #[serde(skip_serializing_if = "Option::is_none")]
    claims_withheld: Option<String>,
}

#[derive(Serialize)]
struct CaseRecord {
    suite: String,
    name: String,
    artifact: String,
    sha256: String,
    cid: String,
    export: String,
    params: Vec<String>,
    class: String,
    args: Vec<Json>,
    expected: Option<Outcome>,
    #[serde(skip_serializing_if = "Option::is_none")]
    expected_detail: Option<String>,
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
    suites: Vec<SuiteRecord>,
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

/// RFC 4648 base32, lowercase, without padding.
fn base32_lower(data: &[u8]) -> String {
    const ALPHA: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";
    let mut out = String::new();
    let (mut acc, mut bits) = (0u32, 0u32);
    for &b in data {
        acc = (acc << 8) | u32::from(b);
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(ALPHA[((acc >> bits) & 31) as usize] as char);
        }
    }
    if bits > 0 {
        out.push(ALPHA[((acc << (5 - bits)) & 31) as usize] as char);
    }
    out
}

/// The CIDv1 of `bytes` as the artifact registry writes it (`sil project lock`): multibase
/// base32 (`b`) of `0x01` (CIDv1), `0x55` (raw), `0x1e 0x20` (BLAKE3-256 multihash) and the
/// digest.
fn cid(bytes: &[u8]) -> String {
    let mut data = vec![0x01, 0x55, 0x1e, 0x20];
    data.extend_from_slice(blake3::hash(bytes).as_bytes());
    format!("b{}", base32_lower(&data))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Run one case: returns the parameter signature and the observation.
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
    let params: Vec<(String, Ty)> = fty
        .params()
        .map(|(n, t)| (n.to_string(), Ty::of(&t)))
        .collect();
    let sig = params
        .iter()
        .map(|(n, t)| format!("{n}: {}", t.name()))
        .collect::<Vec<_>>();
    let results: Vec<Ty> = fty.results().map(|t| Ty::of(&t)).collect();
    if results != [Ty::Bool] {
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
    for ((name, t), a) in params.iter().zip(&case.args) {
        match to_val(t, a) {
            Ok(v) => args.push(v),
            Err(e) => return (sig, obs(Outcome::Unsupported, format!("{name}: {e}"))),
        }
    }
    let mut out = [Val::Bool(false)];
    let observed = match func.call(&mut store, &args, &mut out) {
        Ok(()) => match out[0] {
            Val::Bool(b) => Observed {
                outcome: if b {
                    Outcome::Accepted
                } else {
                    Outcome::Rejected
                },
                detail: None,
            },
            ref v => obs(Outcome::Unsupported, format!("non-bool result {v:?}")),
        },
        Err(e) => match e.downcast_ref::<wasmtime::Trap>() {
            Some(t) => obs(Outcome::Trap, format!("{t}")),
            None => obs(Outcome::Error, format!("{e:#}")),
        },
    };
    (sig, observed)
}

/// `pass`, `fail` or `unchecked`.
fn verdict(case: &Case, observed: &Observed) -> &'static str {
    match case.expect {
        None => "unchecked",
        Some(x) if x != observed.outcome => "fail",
        Some(_) => match &case.expect_detail {
            Some(d)
                if !observed
                    .detail
                    .as_deref()
                    .unwrap_or("")
                    .contains(d.as_str()) =>
            {
                "fail"
            }
            _ => "pass",
        },
    }
}

fn load_suite(path: &Path) -> Result<Suite> {
    let text =
        std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    let suite: Suite =
        serde_json::from_str(&text).with_context(|| format!("parsing {}", path.display()))?;
    for (id, a) in &suite.artifacts {
        if !a.claims.is_empty() && a.sha256.is_none() {
            bail!(
                "{}: artifact {id} has claims but no sha256 pin (a claim is about exact bytes)",
                path.display()
            );
        }
        for c in &a.claims {
            if c.theorems.is_empty() {
                bail!(
                    "{}: artifact {id}: a claim names no theorem",
                    path.display()
                );
            }
        }
    }
    for c in &suite.cases {
        if c.expect_detail.is_some() && c.expect.is_none() {
            bail!(
                "{}: case {}: expect_detail without expect",
                path.display(),
                c.name
            );
        }
    }
    Ok(suite)
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let (config, config_record) = engine_config();
    let engine = Engine::new(&config).map_err(|e| anyhow!("creating the engine: {e:#}"))?;
    let mut report = Report {
        kind: REPORT_KIND,
        evidence: "runtime observations of one engine on concrete inputs; not a proof",
        command: std::env::args().collect(),
        engine: EngineRecord {
            name: "wasmtime",
            version: WASMTIME_VERSION,
            config: config_record,
        },
        suites: vec![],
        artifacts: vec![],
        cases: vec![],
        summary: BTreeMap::new(),
    };
    for suite_path in &cli.suites {
        let suite = load_suite(suite_path)?;
        if !cli.suite_filter.is_empty()
            && !cli
                .suite_filter
                .iter()
                .any(|f| suite.suite.contains(f.as_str()))
        {
            continue;
        }
        let base = suite_path.parent().unwrap_or(Path::new("."));
        let mut loaded: BTreeMap<String, (String, String, Result<Component, String>)> =
            BTreeMap::new();
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
            // A claim is about the pinned bytes: shown only when the file is those bytes.
            let (claims, claims_withheld) = match pinned_ok {
                Some(true) => (
                    spec.claims
                        .iter()
                        .map(|c| ClaimRecord {
                            sha256: sha.clone(),
                            claim: c.clone(),
                        })
                        .collect(),
                    None,
                ),
                _ if spec.claims.is_empty() => (vec![], None),
                _ => (
                    vec![],
                    Some(format!(
                        "{} claim(s) withheld: the file is not the pinned SHA-256",
                        spec.claims.len()
                    )),
                ),
            };
            report.artifacts.push(ArtifactRecord {
                id: format!("{}/{id}", suite.suite),
                path: spec.path.display().to_string(),
                source: spec.source.clone(),
                bytes: bytes.len(),
                sha256: sha.clone(),
                blake3: blake3::hash(&bytes).to_hex().to_string(),
                cid: cid(&bytes),
                pinned_sha256_ok: pinned_ok,
                claims,
                claims_withheld,
            });
            loaded.insert(id.clone(), (sha, cid(&bytes), component));
        }
        report.suites.push(SuiteRecord {
            suite: suite.suite.clone(),
            description: suite.description.clone(),
        });
        for case in &suite.cases {
            let Some((sha, cid, component)) = loaded.get(&case.artifact) else {
                bail!(
                    "{}: case {} names unknown artifact {}",
                    suite.suite,
                    case.name,
                    case.artifact
                );
            };
            if !cli.case.is_empty() && !cli.case.contains(&case.name) {
                continue;
            }
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
            let verdict = verdict(case, &observed);
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
                cid: cid.clone(),
                export: case.export.clone(),
                params,
                class: case.class.clone(),
                args: case.args.clone(),
                expected: case.expect,
                expected_detail: case.expect_detail.clone(),
                observed,
                verdict: verdict.to_string(),
                note: case.note.clone(),
            });
        }
    }
    if report.cases.is_empty() {
        bail!("no case selected (check --suite-filter and --case)");
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

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use wasm_encoder::{
        CanonicalOption, CodeSection, ComponentBuilder, ComponentExportKind, ComponentValType,
        ExportKind, ExportSection, Function, FunctionSection, MemorySection, MemoryType, Module,
        PrimitiveValType, TypeSection, ValType,
    };

    #[test]
    fn base32_rfc4648_vectors() {
        // RFC 4648 section 10, lowercase and unpadded.
        for (input, out) in [
            ("", ""),
            ("f", "my"),
            ("fo", "mzxq"),
            ("foo", "mzxw6"),
            ("foob", "mzxw6yq"),
            ("fooba", "mzxw6ytb"),
            ("foobar", "mzxw6ytboi"),
        ] {
            assert_eq!(base32_lower(input.as_bytes()), out, "{input:?}");
        }
    }

    #[test]
    fn cid_of_known_bytes() {
        // BLAKE3("") = af1349b9…, BLAKE3("abc") = 6437b3ac…, CIDv1 raw, multibase base32
        // (computed independently: `b` + base32(01 55 1e 20 ‖ digest)).
        assert_eq!(
            cid(b""),
            "bafkr4ifpcne3t5pzugtkaqcn5i3nzskjtpfslsnnyejlpte2spfoihzsmi"
        );
        assert_eq!(
            cid(b"abc"),
            "bafkr4ideg6z2yocgkez77nr3outtvdnvjdcvqrs5phnqh7jvtrwnlpm5qu"
        );
        assert_eq!(cid(b"abc").len(), 59);
    }

    fn case(args: Json, expect: Option<Outcome>, detail: Option<&str>) -> Case {
        Case {
            name: "t".into(),
            artifact: "a".into(),
            export: "f".into(),
            class: String::new(),
            args: args.as_array().cloned().unwrap_or_default(),
            expect,
            expect_detail: detail.map(str::to_string),
            note: String::new(),
        }
    }

    #[test]
    fn verdicts() {
        let trap = Observed {
            outcome: Outcome::Trap,
            detail: Some("wasm trap: wasm `unreachable` instruction executed".into()),
        };
        assert_eq!(verdict(&case(json!([]), None, None), &trap), "unchecked");
        assert_eq!(
            verdict(&case(json!([]), Some(Outcome::Trap), None), &trap),
            "pass"
        );
        assert_eq!(
            verdict(
                &case(json!([]), Some(Outcome::Trap), Some("unreachable")),
                &trap
            ),
            "pass"
        );
        assert_eq!(
            verdict(
                &case(json!([]), Some(Outcome::Trap), Some("out of bounds")),
                &trap
            ),
            "fail"
        );
        assert_eq!(
            verdict(&case(json!([]), Some(Outcome::Error), None), &trap),
            "fail"
        );
        let acc = Observed {
            outcome: Outcome::Accepted,
            detail: None,
        };
        assert_eq!(
            verdict(&case(json!([]), Some(Outcome::Accepted), Some("x")), &acc),
            "fail"
        );
    }

    /// A component exporting `f(x: everything) -> bool` that returns `true`, where `everything`
    /// is a record with a field of every supported kind of type. It has more than 16 flat
    /// parameters, so the core function takes one pointer: `(i32) -> i32`.
    fn everything_component() -> Vec<u8> {
        let mut m = Module::new();
        let mut types = TypeSection::new();
        types.ty().function([ValType::I32], [ValType::I32]);
        types.ty().function([ValType::I32; 4], [ValType::I32]);
        m.section(&types);
        let mut funcs = FunctionSection::new();
        funcs.function(0);
        funcs.function(1);
        m.section(&funcs);
        let mut mems = MemorySection::new();
        mems.memory(MemoryType {
            minimum: 1,
            maximum: None,
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        m.section(&mems);
        let mut exps = ExportSection::new();
        exps.export("f", ExportKind::Func, 0);
        exps.export("realloc", ExportKind::Func, 1);
        exps.export("memory", ExportKind::Memory, 0);
        m.section(&exps);
        let mut code = CodeSection::new();
        let mut f = Function::new([]);
        f.instructions().i32_const(1).end();
        code.function(&f);
        // Every allocation at 64 (the function reads nothing, so overlapping is harmless).
        let mut r = Function::new([]);
        r.instructions().i32_const(64).end();
        code.function(&r);
        m.section(&code);

        let p = ComponentValType::Primitive;
        let mut b = ComponentBuilder::default();
        let module = b.core_module(None, &m);
        let inst = b.core_instantiate(None, module, Vec::<(&str, wasm_encoder::ModuleArg)>::new());
        let core_f = b.core_alias_export(None, inst, "f", ExportKind::Func);
        let mem = b.core_alias_export(None, inst, "memory", ExportKind::Memory);
        let realloc = b.core_alias_export(None, inst, "realloc", ExportKind::Func);
        // Named types (exported, as a valid export signature needs).
        let (t, e) = b.ty(None);
        e.defined_type().enum_type(["lt", "le"]);
        let en = b.export("cmp", ComponentExportKind::Type, t, None);
        let (t, e) = b.ty(None);
        e.defined_type().flags(["r", "w"]);
        let fl = b.export("perm", ComponentExportKind::Type, t, None);
        let (t, e) = b.ty(None);
        e.defined_type()
            .variant([("none", None), ("num", Some(p(PrimitiveValType::U16)))]);
        let va = b.export("val", ComponentExportKind::Type, t, None);
        // Anonymous types.
        let (opt, e) = b.ty(None);
        e.defined_type().option(p(PrimitiveValType::U32));
        let (res, e) = b.ty(None);
        e.defined_type().result(
            Some(p(PrimitiveValType::String)),
            Some(ComponentValType::Type(en)),
        );
        let (lst, e) = b.ty(None);
        e.defined_type().list(ComponentValType::Type(va));
        let (tup, e) = b.ty(None);
        e.defined_type()
            .tuple([p(PrimitiveValType::Bool), p(PrimitiveValType::S32)]);
        let (t, e) = b.ty(None);
        e.defined_type().record([
            ("a", p(PrimitiveValType::U8)),
            ("b", p(PrimitiveValType::S8)),
            ("c", p(PrimitiveValType::U16)),
            ("d", p(PrimitiveValType::S16)),
            ("e", p(PrimitiveValType::U64)),
            ("f", p(PrimitiveValType::F32)),
            ("g", p(PrimitiveValType::F64)),
            ("h", p(PrimitiveValType::Char)),
            ("i", p(PrimitiveValType::String)),
            ("j", ComponentValType::Type(opt)),
            ("k", ComponentValType::Type(res)),
            ("l", ComponentValType::Type(lst)),
            ("m", ComponentValType::Type(fl)),
            ("n", ComponentValType::Type(tup)),
        ]);
        let rec = b.export("everything", ComponentExportKind::Type, t, None);
        let (fty, e) = b.ty(None);
        e.function()
            .params([("x", ComponentValType::Type(rec))])
            .result(Some(p(PrimitiveValType::Bool)));
        let lifted = b.lift_func(
            None,
            core_f,
            fty,
            [
                CanonicalOption::UTF8,
                CanonicalOption::Memory(mem),
                CanonicalOption::Realloc(realloc),
            ],
        );
        b.export("f", ComponentExportKind::Func, lifted, None);
        b.finish()
    }

    #[test]
    fn every_supported_type_through_wasmtime() {
        let (config, _) = engine_config();
        let engine = Engine::new(&config).unwrap();
        let component = Component::from_binary(&engine, &everything_component()).unwrap();
        let x = json!({
            "a": 255, "b": -128, "c": 65535, "d": -32768, "e": u64::MAX, "f": "nan", "g": -0.5,
            "h": "λ", "i": "text", "j": {"some": 7},
            "k": {"err": "le"}, "l": [{"case": "none"}, {"case": "num", "value": 3}],
            "m": ["w", "r"], "n": [true, -1]
        });
        let (sig, obs) = run_case(&engine, &component, &case(json!([x]), None, None));
        assert_eq!(
            sig,
            [
                "x: record { a: u8, b: s8, c: u16, d: s16, e: u64, f: f32, g: f64, h: char, \
              i: string, j: option<u32>, k: result<string, enum { lt, le }>, \
              l: list<variant { none, num(u16) }>, m: flags { r, w }, n: tuple<bool, s32> }"
            ]
        );
        assert_eq!(obs.outcome, Outcome::Accepted, "{obs:?}");
        // The other sides of option and result.
        let mut y = x.clone();
        y["j"] = Json::Null;
        y["k"] = json!({"ok": ""});
        y["m"] = json!([]);
        let (_, obs) = run_case(&engine, &component, &case(json!([y]), None, None));
        assert_eq!(obs.outcome, Outcome::Accepted, "{obs:?}");
        // A wrong shape is `unsupported`, naming the parameter, and runs nothing.
        let mut z = x.clone();
        z["j"] = json!(7);
        let (_, obs) = run_case(&engine, &component, &case(json!([z]), None, None));
        assert_eq!(obs.outcome, Outcome::Unsupported);
        assert!(obs.detail.unwrap().starts_with("x: "));
        // Arity and missing exports.
        let (_, obs) = run_case(&engine, &component, &case(json!([]), None, None));
        assert_eq!(obs.outcome, Outcome::Unsupported);
        let mut c = case(json!([x]), None, None);
        c.export = "g".into();
        let (_, obs) = run_case(&engine, &component, &c);
        assert_eq!(
            (obs.outcome, obs.detail.as_deref()),
            (Outcome::Unsupported, Some("no export g"))
        );
    }

    #[test]
    fn suites_parse_and_claims_need_a_pin() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("suites");
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|e| e == "json") {
                load_suite(&path).unwrap();
            }
        }
        let tmp = std::env::temp_dir().join(format!("harness-test-{}.json", std::process::id()));
        std::fs::write(
            &tmp,
            r#"{"suite": "s", "artifacts": {"a": {"path": "x.wasm", "claims": [
                {"kind": "k", "level": "component", "value": "v", "scope": "s",
                 "theorems": [{"decl": "d", "module": "m", "states": "s"}]}]}}, "cases": []}"#,
        )
        .unwrap();
        let err = load_suite(&tmp).err().map(|e| e.to_string());
        std::fs::remove_file(&tmp).unwrap();
        assert!(err.unwrap().contains("no sha256 pin"));
    }
}
