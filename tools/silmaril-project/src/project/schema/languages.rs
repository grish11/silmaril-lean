//! Layer 5, languages: `language_domain`, `measure`, `language_interpretation` and `language`
//! records (Lean: `Silmaril.Project.Registry.Language.Defs`), their tables, and the view that
//! relates the standard language problems (`silmaril.shapes.language.*`) to the languages
//! they are about.
//!
//! A language's `identity` is the JSON description of its construction that Lean fills in
//! (operator, operands' identities, defining constants, CIDs, interpretation, carrier). It
//! contains no display name, so `identity_hash` (BLAKE3 of its compact text) identifies the
//! construction independently of what the language is called. Equality *as sets* of two
//! languages built differently is a problem (`silmaril.shapes.language.eq_at`), never inferred
//! from identities.
use super::*;
use serde::Deserialize;

/// The operations of `language` (Lean's `languageOps`).
pub const LANGUAGE_OPS: [&str; 8] = [
    "decl", "format", "artifact", "union", "inter", "diff", "regex", "within",
];

/// The standard language shapes: `(problem, role of each argument position)`. The roles name
/// what an instance argument is: a language (`L`, `K`), a measure (`mu`), a bound (`b`), the
/// sentence (`x`) or an artifact's bytes (`bytes`).
pub const LANGUAGE_SHAPES: &[(&str, &[&str])] = &[
    ("silmaril.shapes.language.member", &["type", "L", "x"]),
    ("silmaril.shapes.language.bytes_member", &["L", "bytes"]),
    (
        "silmaril.shapes.language.subset_at",
        &["type", "L", "K", "x"],
    ),
    ("silmaril.shapes.language.eq_at", &["type", "L", "K", "x"]),
    (
        "silmaril.shapes.language.bound_at",
        &["type", "L", "mu", "b", "x"],
    ),
    (
        "silmaril.shapes.language.eq_within_at",
        &["type", "L", "K", "mu", "b", "x"],
    ),
];

table! {
    /// `silmaril language_domain NAME := T`; Lean fills `carrier`, `monoid` and `letters`.
    LanguageDomain = "language_domains", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        carrier: String = "TEXT NOT NULL",
        monoid: bool = "INTEGER NOT NULL",
        letters: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    /// `silmaril measure NAME := μ (domain := D)`; Lean fills `codomain`.
    Measure = "measures", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        domain: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        codomain: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    /// `silmaril language_interpretation NAME := I (domain := D) (abi := A) (environment := E)`;
    /// Lean checks that `A` and `E` occur in `I`'s definition and fills `input` and `carrier`.
    LanguageInterpretation = "language_interpretations", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        domain: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        input: String = "TEXT NOT NULL",
        carrier: String = "TEXT NOT NULL",
        abi: Option<String> = "TEXT",
        environment: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

table! {
    /// `silmaril language NAME (domain := D) (op := …) …`; Lean generates or checks `decl` and
    /// fills `carrier` and `identity`. `identity_hash` is BLAKE3 of the compact identity.
    Language = "languages", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        domain: String = "TEXT NOT NULL",
        op: String = "TEXT NOT NULL CHECK(op IN ('decl','format','artifact','union','inter','diff','regex','within'))",
        decl: String = "TEXT NOT NULL",
        carrier: String = "TEXT NOT NULL",
        title: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        source: Option<String> = "TEXT",
        format: Option<String> = "TEXT",
        value: Option<String> = "TEXT",
        interpretation: Option<String> = "TEXT",
        regex: Option<String> = "TEXT",
        semantics: Option<String> = "TEXT CHECK(semantics IN ('list','monoid'))",
        measure: Option<String> = "TEXT",
        bound: Option<i64> = "INTEGER",
        /// The definition as Lean prints it in instance arguments (with its `«…»` escapes);
        /// `None` in dumps written before it existed.
        term: Option<String> = "TEXT",
        identity: serde_json::Value = "TEXT NOT NULL",
        #[serde(skip)] identity_hash: String = "TEXT NOT NULL",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra {
        /// Table `language_operands`: the operands of `union`, `inter`, `diff` and `within`, or
        /// the leaves of `regex`.
        #[serde(default)] args: Vec<String>,
        #[serde(rename = "sid")] sid_override: Option<String>,
    }
}

table! {
    /// Operand `pos` of a language (an operand of a set operation or `within`, or a leaf of a
    /// regular expression).
    LanguageOperand = "language_operands", key("language", "pos") {
        language: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        operand: String = "TEXT NOT NULL",
    }
}

/// The BLAKE3 hash (hex) of a language identity's compact JSON text.
pub fn identity_hash(identity: &serde_json::Value) -> String {
    crate::project::hash::hex(blake3::hash(identity.to_string().as_bytes()).as_bytes())
}

/// The view `language_problems`: one row per argument of an instance of a standard language
/// shape that names a registered language (the argument's recorded term is the language's `term`,
/// both printed by Lean the same way, escapes included), with the instance's
/// shape, role, expected status, summary and verdict. `language_shape_roles` is the role table
/// it reads (the rows of [`LANGUAGE_SHAPES`]).
pub const LANGUAGE_VIEWS: &[&str] = &[
    "CREATE VIEW language_problems AS SELECT i.problem AS problem, e.parent AS shape, \
r.role AS role, i.pos AS pos, l.name AS language, p.expect AS expect, p.title AS title, \
s.summary AS summary, s.verdict AS verdict \
FROM instance_args i JOIN edges e ON e.child = i.problem AND e.kind = 'instance' \
JOIN language_shape_roles r ON r.shape = e.parent AND r.pos = i.pos \
JOIN languages l ON l.term = i.term \
JOIN problems p ON p.name = i.problem LEFT JOIN summary s ON s.problem = i.problem;",
];

table! {
    /// The roles of the arguments of the standard language shapes ([`LANGUAGE_SHAPES`]).
    LanguageShapeRole = "language_shape_roles", key("shape", "pos") {
        shape: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        role: String = "TEXT NOT NULL",
    }
}

/// The rows of `language_shape_roles`.
pub fn shape_role_rows() -> Vec<LanguageShapeRole> {
    LANGUAGE_SHAPES
        .iter()
        .flat_map(|(shape, roles)| {
            roles
                .iter()
                .enumerate()
                .map(|(pos, role)| LanguageShapeRole {
                    shape: (*shape).into(),
                    pos: pos as i64,
                    role: (*role).into(),
                })
        })
        .collect()
}
