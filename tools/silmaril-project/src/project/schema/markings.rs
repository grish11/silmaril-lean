//! Markings: what a project says *about* its problems and specs after looking at the verdicts.
//!
//! - `deprecation` records mark a **wrong** problem, group, spec or language as deprecated, with a reason
//!   and the corrected replacement(s) (`superseded_by`). A deprecated object is never deleted:
//!   it stays in the DAG with its statuses, and the database says it is deprecated.
//! - `finding` records classify the refutation of a failing problem: a genuine defect of the
//!   code under test (`error`), a wrong statement (`spec_bug`, which needs the problem or its
//!   spec to be deprecated), a gap of the machine model the statement is about (`model_gap`,
//!   with a `pointer` to the missing instruction or feature), or `unclear`.
//! - `expected_open` records mark an open problem that is expected to **stay** open for a
//!   metatheoretic reason about the *ambient* theory, the one its proofs are checked in: Lean's
//!   type theory with the axioms the proofs may use (`propext`, `Classical.choice`,
//!   `Quot.sound`). The reason ([`EXPECTED_OPEN_REASONS`]) and the required `note` must hold of
//!   that theory, not of an object theory the statement talks about: Con(ZFC) is not an
//!   example, since Gödel's theorem for ZFC says nothing about Lean, whose universes make it
//!   stronger than ZFC. Lists of open problems leave marked problems out. An ordinary unproved
//!   problem is never marked so.
//!
//! Lean stores all three as generic records (no handler): `silmaril deprecation N (reason :=
//! "…") (superseded_by := [M])`, `silmaril finding N (classification := error) (note := "…")`,
//! `silmaril expected_open N (reason := consistency) (note := "…")`, or the `[[deprecation]]`, `[[finding]]`
//! and `[[expected_open]]` tables of a records file.
use super::*;
use serde::Deserialize;

/// The classifications of a refutation (`finding.classification`).
pub const CLASSIFICATIONS: [&str; 4] = ["error", "spec_bug", "model_gap", "unclear"];
/// The disclosure states of an `error` (`finding.disclosure_status`).
pub const DISCLOSURE_STATES: [&str; 3] = ["private", "reported", "public"];
/// Why a problem is expected to stay open (`expected_open.reason`), always about the ambient
/// theory (Lean's, with the axioms its proofs may use): `independent` (known to be neither
/// provable nor refutable in that theory) or `consistency` (the statement implies the
/// consistency of that theory itself, which, if consistent, cannot prove it by Gödel's second
/// incompleteness theorem). Undecidability of a problem class says nothing about one instance,
/// so it is not a reason.
pub const EXPECTED_OPEN_REASONS: [&str; 2] = ["independent", "consistency"];

/// `silmaril deprecation NAME (reason := "…") (superseded_by := [...])`: the problem, group or
/// spec `NAME` is wrong and kept only for the record.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Deprecation {
    /// The deprecated problem, group or spec.
    pub name: String,
    pub module: String,
    /// Why it is wrong (required; an `Option` so that its absence is a check error).
    pub reason: Option<String>,
    /// The corrected problems, groups or specs that replace it.
    #[serde(default)]
    pub superseded_by: Vec<String>,
}

/// `silmaril finding NAME (classification := …) …`: what the refutation of `NAME` means.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Finding {
    /// The refuted problem.
    pub name: String,
    pub module: String,
    /// One of [`CLASSIFICATIONS`].
    pub classification: String,
    pub note: Option<String>,
    /// What the finding points at: the missing instruction or feature of a `model_gap`, a bug
    /// report, a commit.
    pub pointer: Option<String>,
    /// `error` only: the versions the defect affects.
    #[serde(default)]
    pub affected_versions: Vec<String>,
    /// `error` only: the first fixed version.
    pub fixed_in: Option<String>,
    /// `error` only: one of [`DISCLOSURE_STATES`].
    pub disclosure_status: Option<String>,
}

/// `silmaril expected_open NAME (reason := …) …`: the open problem `NAME` is expected to stay
/// open for a metatheoretic reason.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExpectedOpen {
    /// The problem (not a group).
    pub name: String,
    pub module: String,
    /// One of [`EXPECTED_OPEN_REASONS`] (required; an `Option` so that its absence is a check
    /// error).
    pub reason: Option<String>,
    /// Why the reason holds of the ambient theory (required, M4; an `Option` so that its
    /// absence is a check error).
    pub note: Option<String>,
    /// A citation or URL for the metatheoretic result.
    pub pointer: Option<String>,
}

table! {
    /// Every in-scope `deprecation` record; `kind` is what `name` is.
    DeprecationRow = "deprecations", key("name") {
        name: String = "TEXT NOT NULL",
        kind: String = "TEXT NOT NULL CHECK(kind IN ('problem','group','spec','language'))",
        reason: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        origin: String = "TEXT NOT NULL CHECK(origin IN ('local','imported'))",
    }
}

table! {
    /// The replacements of a deprecation, in order; `kind` is what `replacement` is.
    Replacement = "deprecation_replacements", key("name", "pos") {
        name: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        replacement: String = "TEXT NOT NULL",
        kind: String = "TEXT NOT NULL CHECK(kind IN ('problem','group','spec','language'))",
    }
}

table! {
    /// Every in-scope problem or group that is deprecated, and why: `self` (its own
    /// `deprecation`), `spec` (its judgement's spec is deprecated) or `instance` (it is an
    /// instance of a deprecated problem); `via` is the deprecated name.
    DeprecatedProblem = "deprecated_problems", key("problem") {
        problem: String = "TEXT NOT NULL",
        via_kind: String = "TEXT NOT NULL CHECK(via_kind IN ('self','spec','instance'))",
        via: String = "TEXT NOT NULL",
    }
}

table! {
    /// Every in-scope `finding`: the classification of a failing problem's refutation.
    FindingRow = "findings", key("problem") {
        problem: String = "TEXT NOT NULL",
        classification: String = "TEXT NOT NULL CHECK(classification IN ('error','spec_bug','model_gap','unclear'))",
        note: Option<String> = "TEXT",
        pointer: Option<String> = "TEXT",
        fixed_in: Option<String> = "TEXT",
        disclosure_status: Option<String> = "TEXT CHECK(disclosure_status IN ('private','reported','public'))",
        module: String = "TEXT NOT NULL",
        origin: String = "TEXT NOT NULL CHECK(origin IN ('local','imported'))",
    }
}

table! {
    /// The versions an `error` finding affects, in order.
    FindingVersion = "finding_versions", key("problem", "pos") {
        problem: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        version: String = "TEXT NOT NULL",
    }
}

table! {
    /// Every in-scope `expected_open`: a problem expected to stay open for a metatheoretic
    /// reason (lists of open problems leave it out).
    ExpectedOpenRow = "expected_open", key("problem") {
        problem: String = "TEXT NOT NULL",
        reason: String = "TEXT NOT NULL CHECK(reason IN ('independent','consistency'))",
        note: Option<String> = "TEXT",
        pointer: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        origin: String = "TEXT NOT NULL CHECK(origin IN ('local','imported'))",
    }
}

/// The marking views (in [`super::VIEWS`]): the queries the guide documents.
pub const MARKING_VIEWS: &[&str] = &[
    "CREATE VIEW genuine_errors AS SELECT f.problem, p.title, s.summary, f.note, f.pointer, \
(SELECT group_concat(v.version, ',') FROM (SELECT version FROM finding_versions WHERE problem = f.problem ORDER BY pos) v) AS affected_versions, \
f.fixed_in, f.disclosure_status, f.module, f.origin \
FROM findings f JOIN problems p ON p.name = f.problem LEFT JOIN summary s ON s.problem = f.problem \
WHERE f.classification = 'error';",
    "CREATE VIEW model_gaps AS SELECT f.pointer, f.problem, p.title, f.note \
FROM findings f JOIN problems p ON p.name = f.problem WHERE f.classification = 'model_gap';",
    "CREATE VIEW spec_bugs AS SELECT f.problem, d.via_kind, d.via, f.note, f.pointer \
FROM findings f LEFT JOIN deprecated_problems d ON d.problem = f.problem \
WHERE f.classification = 'spec_bug';",
    "CREATE VIEW deprecated_with_replacements AS SELECT d.name, d.kind, d.reason, \
(SELECT group_concat(r.replacement, ',') FROM (SELECT replacement FROM deprecation_replacements WHERE name = d.name ORDER BY pos) r) AS superseded_by, \
d.module, d.origin FROM deprecations d;",
    "CREATE VIEW unclassified_failures AS SELECT s.problem, s.summary FROM summary s \
WHERE s.verdict = 'fails' AND s.problem NOT IN (SELECT problem FROM findings) \
AND s.problem NOT IN (SELECT problem FROM deprecated_problems);",
];

/// The rules between a finding's keys (as JSON, from a records table or a dump record): the
/// `error`-only keys appear only on an `error`, and a `model_gap` has a `pointer`.
pub fn finding_key_errors(
    keys: &std::collections::BTreeMap<String, serde_json::Value>,
) -> Vec<String> {
    let class = keys.get("classification").and_then(|v| v.as_str());
    let mut out = Vec::new();
    if class != Some("error") {
        for k in ["affected_versions", "fixed_in", "disclosure_status"] {
            if keys.contains_key(k) {
                out.push(format!("`{k}` is for `error` findings only"));
            }
        }
    }
    if class == Some("model_gap") && !keys.contains_key("pointer") {
        out.push("a `model_gap` needs a `pointer` (the missing instruction or feature)".into());
    }
    out
}

impl Finding {
    /// [`finding_key_errors`] of the record.
    pub fn key_errors(&self) -> Vec<String> {
        let mut keys = std::collections::BTreeMap::new();
        keys.insert(
            "classification".to_string(),
            serde_json::json!(self.classification),
        );
        if !self.affected_versions.is_empty() {
            keys.insert(
                "affected_versions".into(),
                serde_json::json!(self.affected_versions),
            );
        }
        for (k, v) in [
            ("pointer", &self.pointer),
            ("fixed_in", &self.fixed_in),
            ("disclosure_status", &self.disclosure_status),
        ] {
            if let Some(v) = v {
                keys.insert(k.into(), serde_json::json!(v));
            }
        }
        finding_key_errors(&keys)
    }
}
