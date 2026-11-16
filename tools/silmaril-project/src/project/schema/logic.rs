//! Layer 4, the logic graph (docs/projects/logic-graph.md): institutions, comorphisms and
//! morphisms (`Silmaril/Project/Registry/Institution/Defs.lean`), with rooms ([`super::rooms`])
//! and corridors one level down; the facts proved about edges; the audit of the declarations the
//! registry omits; and the pinned Hets logic graph the records relate to.
//!
//! Lean checks every declaration's type and finds the endpoints of every edge among the
//! registered nodes (`from`/`to`, stored as the columns `src`/`dst`). An edge is directed as Lean
//! writes its type, `Inst.CoHom A B`, `Inst.Hom A B` or `Corridor R₁ R₂`: from `A` to `B`. What
//! travels which way depends on the kind of edge (see [`EDGE_KINDS`]); no row records a property
//! that a fact does not prove.
use super::*;

/// The node kinds and edge kinds of the logic graph, with what moves which way along an edge
/// `A → B` (`(kind, sentences, models)`).
pub const EDGE_KINDS: &[(&str, &str, &str)] = &[
    (
        "comorphism",
        "forwards: Sen_A Σ → Sen_B (Φ Σ)",
        "backwards: Mod_B (Φ Σ) → Mod_A Σ",
    ),
    (
        "morphism",
        "backwards: Sen_B (Φ Σ) → Sen_A Σ",
        "forwards: Mod_A Σ → Mod_B (Φ Σ)",
    ),
    (
        "corridor",
        "forwards: Sen₁ → Sen₂",
        "backwards: Mod₂ → Mod₁",
    ),
];

/// How a record relates to a logic or comorphism of the Hets logic graph.
pub const HETS_RELATIONS: [&str; 3] = ["corresponds", "fragment", "related"];

/// The properties a fact may state (Lean's `logicFacts`): `(record kind, property)`.
pub const LOGIC_FACTS: &[(&str, &str)] = &[
    ("comorphism", "model_expansive"),
    ("morphism", "sound"),
    ("corridor", "model_expansive"),
];

/// One fact about an edge: a theorem stating a known property, with its axioms.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LogicFactSpec {
    pub property: String,
    pub proof: String,
    #[serde(default)]
    pub axioms: Vec<String>,
    /// The arguments of the one instance of a family the fact is about (none: every instance).
    #[serde(default, rename = "at")]
    pub at: Option<String>,
}

table! {
    /// `silmaril institution NAME := I`, with `I : Silmaril.Logic.Institution.Inst` or a family
    /// `∀ x⃗, Inst` (`arity` binders, printed in `params`); Lean fills `type`, `levels` (the
    /// universe parameters) and `doc` (the docstring, unless given). `hets` names a logic of the
    /// Hets logic graph and `hets_relation` how this institution relates to it.
    Institution = "institutions", key("sid"), unique("name") {
        #[serde(skip)] sid: String = "TEXT NOT NULL",
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        arity: i64 = "INTEGER NOT NULL",
        params: Option<String> = "TEXT",
        r#type: String = "TEXT NOT NULL",
        levels: String = "TEXT NOT NULL",
        title: Option<String> = "TEXT",
        doc: Option<String> = "TEXT",
        source: Option<String> = "TEXT",
        scope: Option<String> = "TEXT",
        hets: Option<String> = "TEXT",
        hets_relation: Option<String> = "TEXT CHECK(hets_relation IN ('corresponds','fragment','related'))",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
    extra { #[serde(rename = "sid")] sid_override: Option<String>, }
}

/// The edge records share their fields: `comorphism`, `morphism` and `corridor`.
macro_rules! edge_table {
    ($(#[$m:meta])* $name:ident = $table:literal) => {
        table! {
            $(#[$m])*
            $name = $table, key("sid"), unique("name") {
                #[serde(skip)] sid: String = "TEXT NOT NULL",
                name: String = "TEXT NOT NULL",
                decl: String = "TEXT NOT NULL",
                #[serde(rename = "from")] src: String = "TEXT NOT NULL",
                #[serde(rename = "to")] dst: String = "TEXT NOT NULL",
                from_at: Option<String> = "TEXT",
                to_at: Option<String> = "TEXT",
                arity: i64 = "INTEGER NOT NULL",
                params: Option<String> = "TEXT",
                r#type: String = "TEXT NOT NULL",
                levels: String = "TEXT NOT NULL",
                title: Option<String> = "TEXT",
                doc: Option<String> = "TEXT",
                source: Option<String> = "TEXT",
                scope: Option<String> = "TEXT",
                hets: Option<String> = "TEXT",
                hets_relation: Option<String> = "TEXT CHECK(hets_relation IN ('corresponds','fragment','related'))",
                module: String = "TEXT NOT NULL",
                #[serde(skip)] origin: String = "TEXT NOT NULL",
            }
            extra {
                /// Table `logic_facts`.
                #[serde(default)] facts: Vec<LogicFactSpec>,
                #[serde(rename = "sid")] sid_override: Option<String>,
            }
        }
    };
}

edge_table! {
    /// `silmaril comorphism NAME := f`, `f : Inst.CoHom A B` (or a family): a logic translation
    /// from the institution `src` to `dst`, sentences forwards and models backwards. `from_at` and
    /// `to_at` are the arguments of the endpoints when they are families.
    Comorphism = "comorphisms"
}
edge_table! {
    /// `silmaril morphism NAME := f`, `f : Inst.Hom A B` (or a family): a logic projection from
    /// `src` to `dst`, sentences backwards and models forwards.
    Morphism = "morphisms"
}
edge_table! {
    /// `silmaril corridor NAME := c`, `c : Corridor R₁ R₂` (or a family): between the rooms `src`
    /// and `dst`, sentences forwards and models backwards.
    Corridor = "corridors"
}

table! {
    /// The kinds of edge of the logic graph ([`EDGE_KINDS`]), at their level, with what moves
    /// which way along an edge `A → B`.
    LogicEdgeKind = "logic_edge_kinds", key("kind") {
        kind: String = "TEXT NOT NULL",
        level: String = "TEXT NOT NULL",
        sentences: String = "TEXT NOT NULL",
        models: String = "TEXT NOT NULL",
    }
}

/// The rows of `logic_edge_kinds`.
pub fn edge_kind_rows() -> Vec<LogicEdgeKind> {
    EDGE_KINDS
        .iter()
        .map(|(k, s, m)| LogicEdgeKind {
            kind: (*k).into(),
            level: if *k == "corridor" {
                "room"
            } else {
                "institution"
            }
            .into(),
            sentences: (*s).into(),
            models: (*m).into(),
        })
        .collect()
}

table! {
    /// Fact `pos` of the edge `(kind, edge)`: the theorem `proof` states `property` of it (of
    /// every instance of a family, or only at the arguments `instance_at`).
    LogicFact = "logic_facts", key("kind", "edge", "pos") {
        kind: String = "TEXT NOT NULL CHECK(kind IN ('comorphism','morphism','corridor'))",
        edge: String = "TEXT NOT NULL",
        pos: i64 = "INTEGER NOT NULL",
        property: String = "TEXT NOT NULL",
        proof: String = "TEXT NOT NULL",
        instance_at: Option<String> = "TEXT",
        axioms: serde_json::Value = "TEXT NOT NULL",
        standard_axioms: bool = "INTEGER NOT NULL",
    }
}

table! {
    /// `silmaril logic_audit (prefix := P)`: one row per declaration under `scope` that is not a
    /// theorem and whose type is (a family of) an institution, comorphism, morphism, room or
    /// corridor (`object`), with its `arity` (0: closed), module and `layer` (`header`, `proofs`
    /// or `raw`), whether it is `generic` (a construction over an arbitrary institution, room or map,
    /// which no record can name endpoints of), and the record that registers it (`registered`,
    /// null when the registry omits it).
    LogicAudit = "logic_audit", key("name") {
        name: String = "TEXT NOT NULL",
        decl: String = "TEXT NOT NULL",
        object: String = "TEXT NOT NULL CHECK(object IN ('institution','comorphism','morphism','room','corridor'))",
        arity: i64 = "INTEGER NOT NULL",
        #[serde(default)] generic: bool = "INTEGER NOT NULL DEFAULT 0",
        decl_module: String = "TEXT NOT NULL",
        layer: String = "TEXT NOT NULL CHECK(layer IN ('header','proofs','raw'))",
        scope: String = "TEXT NOT NULL",
        registered: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

table! {
    /// A logic of the Hets logic graph (`silmaril/logic-graph/hets.toml`, copied from the pinned
    /// Hets sources): `hets_name` as Hets spells it, the CPP flag that guards it in Hets's build
    /// (null: always built) and the Hets source file that lists it.
    HetsLogic = "hets_logics", key("name") {
        name: String = "TEXT NOT NULL",
        hets_name: String = "TEXT NOT NULL UNIQUE",
        title: Option<String> = "TEXT",
        flag: Option<String> = "TEXT",
        hets_file: String = "TEXT NOT NULL",
        hets_rev: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

table! {
    /// A comorphism of the Hets logic graph, from the logic `hets_from` to `hets_to` (Hets
    /// spellings; a Hets sublogic is named as its logic, with the sublogic in `doc`).
    HetsComorphism = "hets_comorphisms", key("name") {
        name: String = "TEXT NOT NULL",
        hets_name: String = "TEXT NOT NULL UNIQUE",
        hets_from: String = "TEXT NOT NULL",
        hets_to: String = "TEXT NOT NULL",
        flag: Option<String> = "TEXT",
        hets_file: String = "TEXT NOT NULL",
        hets_rev: String = "TEXT NOT NULL",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

table! {
    /// A logic family with Lean developments that are not in this repository yet (listed so that
    /// the omission is explicit; nothing in it is registered or claimed): its title, how many
    /// institutions (`nodes`) and maps (`edges`) it has there, and its `status`.
    LogicPending = "logic_pending", key("name") {
        name: String = "TEXT NOT NULL",
        title: String = "TEXT NOT NULL",
        nodes: i64 = "INTEGER NOT NULL",
        edges: i64 = "INTEGER NOT NULL",
        status: String = "TEXT NOT NULL CHECK(status IN ('pending-port','in-review'))",
        doc: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

/// The statuses of a catalogue entry (`logic_catalogue`, Lean's `catalogueStatuses`).
pub const CATALOGUE_STATUSES: [&str; 4] = [
    "registered",
    "represented",
    "not-institution-typed",
    "prospective",
];

table! {
    /// One entry of the curated catalogue the logic-graph port started from (`silmaril/logic-graph/
    /// catalogue.toml`): its stable `catalogue_id`, `title`, whether it is a logic (`node`) or a map
    /// (`edge`), its `status`, the registered records that hold it (`records`, `kind:name`, JSON), the
    /// Lean declarations that are its evidence (`evidence`, JSON; Lean checked that they exist) and
    /// the `reason` when it is not a registered record.
    LogicCatalogue = "logic_catalogue", key("name") {
        name: String = "TEXT NOT NULL",
        catalogue_id: String = "TEXT NOT NULL UNIQUE",
        title: String = "TEXT NOT NULL",
        entry: String = "TEXT NOT NULL CHECK(entry IN ('node','edge'))",
        status: String = "TEXT NOT NULL CHECK(status IN ('registered','represented','not-institution-typed','prospective'))",
        #[serde(default)] records: serde_json::Value = "TEXT NOT NULL",
        #[serde(default)] evidence: serde_json::Value = "TEXT NOT NULL",
        reason: Option<String> = "TEXT",
        module: String = "TEXT NOT NULL",
        #[serde(skip)] origin: String = "TEXT NOT NULL",
    }
}

/// The views of the logic graph:
/// * `logic_edges`: every edge with its kind, endpoints and level (`institution` or `room`), and
///   how many facts it has;
/// * `logic_nodes`: every node (institutions and rooms) with its level and degree;
/// * `logic_coverage`: per audited object kind and layer, how many declarations there are, how
///   many are closed, and how many are registered;
/// * `hets_coverage`: per Hets logic or comorphism, the records related to it, by relation.
pub const LOGIC_VIEWS: &[&str] = &[
    "CREATE VIEW logic_edges AS \
SELECT 'comorphism' AS kind, 'institution' AS level, name, decl, src, dst, from_at, to_at, arity, title, hets, hets_relation, module, \
(SELECT count(*) FROM logic_facts f WHERE f.kind = 'comorphism' AND f.edge = c.name) AS facts FROM comorphisms c \
UNION ALL SELECT 'morphism', 'institution', name, decl, src, dst, from_at, to_at, arity, title, hets, hets_relation, module, \
(SELECT count(*) FROM logic_facts f WHERE f.kind = 'morphism' AND f.edge = m.name) FROM morphisms m \
UNION ALL SELECT 'corridor', 'room', name, decl, src, dst, from_at, to_at, arity, title, hets, hets_relation, module, \
(SELECT count(*) FROM logic_facts f WHERE f.kind = 'corridor' AND f.edge = r.name) FROM corridors r;",
    "CREATE VIEW logic_nodes AS \
SELECT 'institution' AS kind, name, decl, arity, title, hets, hets_relation, NULL AS institution, module, \
(SELECT count(*) FROM logic_edges e WHERE e.level = 'institution' AND (e.src = i.name OR e.dst = i.name)) AS degree, \
(SELECT count(*) FROM rooms r WHERE r.institution = i.name) AS rooms FROM institutions i \
UNION ALL SELECT 'room', name, decl, arity, title, NULL, NULL, institution, module, \
(SELECT count(*) FROM logic_edges e WHERE e.level = 'room' AND (e.src = r.name OR e.dst = r.name)), NULL FROM rooms r;",
    "CREATE VIEW logic_catalogue_summary AS SELECT entry, status, count(*) AS entries \
FROM logic_catalogue GROUP BY entry, status;",
    "CREATE VIEW logic_coverage AS SELECT object, layer, count(*) AS declarations, \
sum(arity = 0) AS closed, sum(generic) AS generic, sum(registered IS NOT NULL) AS registered, \
sum(registered IS NULL AND NOT generic) AS omitted, sum(registered IS NULL AND generic) AS omitted_generic \
FROM logic_audit GROUP BY object, layer;",
    "CREATE VIEW hets_coverage AS \
SELECT 'logic' AS hets_kind, h.hets_name, h.flag, \
(SELECT group_concat(i.name || ':' || i.hets_relation, ' ') FROM institutions i WHERE i.hets = h.hets_name) AS records, \
(SELECT count(*) FROM institutions i WHERE i.hets = h.hets_name AND i.hets_relation = 'corresponds') AS corresponds, \
(SELECT count(*) FROM institutions i WHERE i.hets = h.hets_name) AS related FROM hets_logics h \
UNION ALL SELECT 'comorphism', h.hets_name, h.flag, \
(SELECT group_concat(e.name || ':' || e.hets_relation, ' ') FROM logic_edges e WHERE e.hets = h.hets_name) AS records, \
(SELECT count(*) FROM logic_edges e WHERE e.hets = h.hets_name AND e.hets_relation = 'corresponds'), \
(SELECT count(*) FROM logic_edges e WHERE e.hets = h.hets_name) FROM hets_comorphisms h;",
];

/// The rows of `logic_facts` of one edge record.
pub fn fact_rows(kind: &str, edge: &str, facts: &[LogicFactSpec]) -> Vec<LogicFact> {
    facts
        .iter()
        .enumerate()
        .map(|(pos, f)| {
            let mut axioms = f.axioms.clone();
            axioms.sort();
            LogicFact {
                kind: kind.into(),
                edge: edge.into(),
                pos: pos as i64,
                property: f.property.clone(),
                proof: f.proof.clone(),
                instance_at: f.at.clone(),
                standard_axioms: axioms.iter().all(|a| STANDARD_AXIOMS.contains(&a.as_str())),
                axioms: serde_json::Value::from(axioms),
            }
        })
        .collect()
}
