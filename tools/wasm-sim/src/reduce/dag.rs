//! The problem DAG, schema `silmaril.wasm-sim.dag.v0` (`docs/projects/wasm-sim-reduction.md`, "DAG schema").
//!
//! A DAG has one **root** (the ISA problem), **nodes** and **edges**. An edge `goal ⇐ pieces`
//! says: solutions of all `pieces` give a solution of `goal`, by the Lean theorem `theorem`
//! (status `proved`), by a composition theorem still owed (`task`), or only checked by tests
//! (`tested`). Several edges may have the same goal (alternative decompositions). A node's
//! `status` is what is known of it alone: `open`, `solved` (with `solution`, a Lean theorem),
//! `refuted` (with `refutation`), or `tested`. The **derived** status of a node is `solved` if
//! it is solved, or if some `proved` edge has it as goal and all its pieces are derived
//! solved; `check` computes it.

use anyhow::{Result, bail};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

pub const SCHEMA: &str = "silmaril.wasm-sim.dag.v0";

/// Node kinds.
pub const KINDS: &[&str] = &[
    "isa-problem",
    "wasm-problem",
    "wasm-piece",
    "translation-validation",
    "simulator-soundness",
    "side-condition",
];
pub const NODE_STATUS: &[&str] = &["open", "solved", "refuted", "tested"];
/// `open` is accepted as a synonym of `task` (the RV64 emitter's spelling).
pub const EDGE_STATUS: &[&str] = &["proved", "task", "tested", "open"];

#[derive(Serialize, Deserialize, Clone, Debug, Default)]
pub struct Node {
    pub id: String,
    pub kind: String,
    #[serde(default = "open")]
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub statement: Option<String>,
    /// The Lean statement (a closed `Prop`, or a term with named parameters).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean: Option<String>,
    /// The Lean theorem solving it, when `solved`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub solution: Option<String>,
    /// The Lean theorem refuting it, when `refuted`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub refutation: Option<String>,
    /// The `silmaril.problem.v1` ID, when registered.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub problem: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub files: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub solvers: Vec<String>,
}

fn open() -> String {
    "open".into()
}

#[derive(Serialize, Deserialize, Clone, Debug, Default)]
pub struct Edge {
    pub goal: String,
    pub pieces: Vec<String>,
    /// The Lean composition theorem (for `proved`), or the owed statement (for `task`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theorem: Option<String>,
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

#[derive(Serialize, Deserialize, Clone, Debug, Default)]
pub struct Dag {
    pub schema: String,
    pub id: String,
    #[serde(default)]
    pub title: String,
    pub root: String,
    /// Free-form descriptions: artifact (ELF, hash), ISA model, simulator, Lean modules.
    #[serde(default, skip_serializing_if = "serde_json::Value::is_null")]
    pub artifact: serde_json::Value,
    #[serde(default, skip_serializing_if = "serde_json::Value::is_null")]
    pub isa: serde_json::Value,
    #[serde(default, skip_serializing_if = "serde_json::Value::is_null")]
    pub sim: serde_json::Value,
    #[serde(default, skip_serializing_if = "serde_json::Value::is_null")]
    pub lean: serde_json::Value,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
}

impl Dag {
    pub fn new(id: &str, title: &str, root: &str) -> Dag {
        Dag {
            schema: SCHEMA.into(),
            id: id.into(),
            title: title.into(),
            root: root.into(),
            ..Default::default()
        }
    }

    pub fn node(&mut self, n: Node) {
        if !self.nodes.iter().any(|m| m.id == n.id) {
            self.nodes.push(n);
        }
    }

    pub fn edge(
        &mut self,
        goal: &str,
        pieces: Vec<String>,
        theorem: &str,
        status: &str,
        note: &str,
    ) {
        self.edges.push(Edge {
            goal: goal.into(),
            pieces,
            theorem: (!theorem.is_empty()).then(|| theorem.into()),
            status: status.into(),
            note: (!note.is_empty()).then(|| note.into()),
        });
    }

    /// Node IDs that no edge decomposes: the independent problems.
    pub fn leaves(&self) -> Vec<&Node> {
        let goals: BTreeSet<&str> = self.edges.iter().map(|e| e.goal.as_str()).collect();
        self.nodes
            .iter()
            .filter(|n| !goals.contains(n.id.as_str()))
            .collect()
    }

    /// The derived status: solved nodes, closed under `proved` edges.
    pub fn derived_solved(&self) -> BTreeSet<String> {
        let mut solved: BTreeSet<String> = self
            .nodes
            .iter()
            .filter(|n| n.status == "solved")
            .map(|n| n.id.clone())
            .collect();
        loop {
            let before = solved.len();
            for e in &self.edges {
                if e.status == "proved" && e.pieces.iter().all(|p| solved.contains(p)) {
                    solved.insert(e.goal.clone());
                }
            }
            if solved.len() == before {
                return solved;
            }
        }
    }
}

/// Statistics of a valid DAG.
pub struct Stats {
    pub nodes: usize,
    pub leaves: usize,
    pub solved: usize,
    pub edges: BTreeMap<String, usize>,
    pub derived: BTreeSet<String>,
    pub root_solved: bool,
}

/// Validate a DAG: schema, unique IDs, known kinds and statuses, edges between existing nodes,
/// solved nodes name a solution, proved edges name a theorem, the root exists, no cycle.
pub fn check(d: &Dag) -> Result<Stats> {
    if d.schema != SCHEMA {
        bail!("schema is {:?}, expected {SCHEMA}", d.schema);
    }
    let mut ids = BTreeSet::new();
    for n in &d.nodes {
        if !ids.insert(n.id.as_str()) {
            bail!("duplicate node {}", n.id);
        }
        if !KINDS.contains(&n.kind.as_str()) {
            bail!(
                "node {}: unknown kind {:?} (one of {KINDS:?})",
                n.id,
                n.kind
            );
        }
        if !NODE_STATUS.contains(&n.status.as_str()) {
            bail!("node {}: unknown status {:?}", n.id, n.status);
        }
        if n.status == "solved" && n.solution.is_none() {
            bail!("node {}: solved without `solution`", n.id);
        }
        if n.status == "refuted" && n.refutation.is_none() {
            bail!("node {}: refuted without `refutation`", n.id);
        }
    }
    if !ids.contains(d.root.as_str()) {
        bail!("root {} is not a node", d.root);
    }
    let mut edges = BTreeMap::new();
    for e in &d.edges {
        if !EDGE_STATUS.contains(&e.status.as_str()) {
            bail!(
                "edge {}: unknown status {:?} (one of {EDGE_STATUS:?})",
                e.goal,
                e.status
            );
        }
        if e.status == "proved" && e.theorem.is_none() {
            bail!("edge {}: proved without `theorem`", e.goal);
        }
        for x in std::iter::once(&e.goal).chain(&e.pieces) {
            if !ids.contains(x.as_str()) {
                bail!("edge {} ⇐ {:?}: no node {x}", e.goal, e.pieces);
            }
        }
        *edges
            .entry(if e.status == "open" {
                "task".to_string()
            } else {
                e.status.clone()
            })
            .or_insert(0) += 1;
    }
    // acyclic: depth-first search over goal -> piece
    let mut adj: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for e in &d.edges {
        adj.entry(e.goal.as_str())
            .or_default()
            .extend(e.pieces.iter().map(|p| p.as_str()));
    }
    fn visit<'a>(
        n: &'a str,
        adj: &BTreeMap<&'a str, Vec<&'a str>>,
        st: &mut BTreeMap<&'a str, u8>,
    ) -> Result<()> {
        match st.get(n) {
            Some(2) => return Ok(()),
            Some(1) => bail!("cycle through {n}"),
            _ => {}
        }
        st.insert(n, 1);
        for m in adj.get(n).into_iter().flatten() {
            visit(m, adj, st)?;
        }
        st.insert(n, 2);
        Ok(())
    }
    let mut st = BTreeMap::new();
    for n in &d.nodes {
        visit(&n.id, &adj, &mut st)?;
    }
    let derived = d.derived_solved();
    Ok(Stats {
        nodes: d.nodes.len(),
        leaves: d.leaves().len(),
        solved: d.nodes.iter().filter(|n| n.status == "solved").count(),
        edges,
        root_solved: derived.contains(&d.root),
        derived,
    })
}

/// The standard per-function edges of an ISA problem reduced through a P-calls translation
/// (`docs/projects/wasm-sim-reduction.md`): `isa/f ⇐ wasm/f, sim/sound, sim/encodes/f`
/// (`Silmaril.Sim.Reduce.specReduction`), `wasm/f ⇐ ag/g` for `g` in `f`'s callee closure
/// (`agDecomp`), and `ag/f ⇐ wasm-ag/f, method/*, tv/f` (P-calls soundness, a task).
pub struct FnInfo {
    pub name: String,
    pub isa_statement: String,
    pub isa_lean: Option<String>,
    pub closure: Vec<String>,
    pub methods: Vec<String>,
    pub module: String,
    pub piece: String,
    pub wasm_lean: Option<String>,
    pub wasm_solution: Option<String>,
    pub wasm_problem: Option<String>,
    /// Loop heads (cut points) with the plan's invariants: `cut/f/<addr>` pieces.
    pub cuts: Vec<String>,
}

pub fn add_function(d: &mut Dag, f: &FnInfo) {
    let n = &f.name;
    d.node(Node {
        id: format!("isa/{n}"),
        kind: "isa-problem".into(),
        status: "open".into(),
        statement: Some(f.isa_statement.clone()),
        lean: f.isa_lean.clone(),
        ..Default::default()
    });
    d.node(Node {
        id: format!("wasm/{n}"),
        kind: "wasm-problem".into(),
        status: "open".into(),
        statement: Some(format!("the sound simulator, from every loadable state meeting the pulled-back entry of `{n}`, can halt in a state meeting the pulled-back result (specWasm)")),
        ..Default::default()
    });
    d.node(Node {
        id: format!("sim/encodes/{n}"),
        kind: "side-condition".into(),
        status: "open".into(),
        statement: Some(format!(
            "every entry state of `{n}` is represented by a loadable simulator state (Encodes)"
        )),
        lean: Some("Silmaril.Sim.Reduce.Encodes".into()),
        ..Default::default()
    });
    d.edge(
        &format!("isa/{n}"),
        vec![format!("wasm/{n}"), "sim/sound".into(), format!("sim/encodes/{n}")],
        "Silmaril.Sim.Reduce.specReduction",
        "proved",
        "Wasm solution + sound simulator + loadable entries => ISA solution; refutations transfer given Complete (isaCex_of_wasmCex)",
    );
    d.edge(
        &format!("wasm/{n}"),
        f.closure.iter().map(|c| format!("ag/{c}")).collect(),
        "Silmaril.Sim.Reduce.agDecomp",
        "proved",
        "assume-guarantee over the acyclic call graph",
    );
    d.node(Node {
        id: format!("ag/{n}"),
        kind: "wasm-piece".into(),
        status: "open".into(),
        statement: Some(format!(
            "AGPiece: `{n}`'s Wasm problem assuming its callees'"
        )),
        lean: Some("Silmaril.Sim.Reduce.AGPiece".into()),
        files: vec![f.module.clone(), f.piece.clone()],
        ..Default::default()
    });
    d.node(Node {
        id: format!("wasm-ag/{n}"),
        kind: "wasm-piece".into(),
        status: if f.wasm_solution.is_some() { "solved".into() } else { "open".into() },
        statement: Some(format!("the module of `{n}` meets its contract relative to the simulator methods' and its callees' specifications")),
        lean: f.wasm_lean.clone(),
        solution: f.wasm_solution.clone(),
        problem: f.wasm_problem.clone(),
        files: vec![f.module.clone(), f.piece.clone()],
        solvers: vec!["wpc/HWP tactics".into(), "wasm-vc sym".into(), "agent".into()],
        ..Default::default()
    });
    d.node(Node {
        id: format!("tv/{n}"),
        kind: "translation-validation".into(),
        status: "open".into(),
        statement: Some(format!("{} performs, block by block, the method calls of the instructions `{n}`'s bytes decode to", f.module)),
        files: vec![f.module.clone()],
        ..Default::default()
    });
    let mut pieces = vec![format!("wasm-ag/{n}")];
    for m in &f.methods {
        let id = format!("method/{m}");
        d.node(Node {
            id: id.clone(),
            kind: "wasm-piece".into(),
            status: "open".into(),
            statement: Some(format!("the simulator's `{m}` meets its specification and refines the reference semantics of its forms (a Silmaril.Sim.Reduce.StepPiece)")),
            solvers: vec!["Wasm refinement/equivalence".into(), "wpc".into()],
            ..Default::default()
        });
        pieces.push(id);
    }
    pieces.push(format!("tv/{n}"));
    d.edge(
        &format!("ag/{n}"),
        pieces,
        "Task: P-calls soundness (methods sound w.r.t. the ISA + translation validity)",
        "task",
        "",
    );
    if !f.cuts.is_empty() {
        let mut cp = vec![format!("cut/{n}/entry")];
        cp.extend(f.cuts.iter().map(|c| format!("cut/{n}/{c}")));
        for id in &cp {
            d.node(Node {
                id: id.clone(),
                kind: "wasm-piece".into(),
                status: "open".into(),
                statement: Some("CutPiece: from this cut with its invariant, reach the exit or a cut with a smaller measure".into()),
                lean: Some("Silmaril.Sim.Reduce.CutPiece".into()),
                files: vec![f.module.clone()],
                ..Default::default()
            });
        }
        d.edge(
            &format!("wasm-ag/{n}"),
            cp,
            "Silmaril.Sim.Reduce.cut_compose",
            "proved",
            "per cut point; the entry is the cut with the precondition as invariant",
        );
    }
}

/// The simulator-level nodes: `sim/sound` from the method pieces and the translation-validation
/// pieces (task), or from another representation and a refinement (`SoundSim.ofRefines`).
pub fn add_simulator(
    d: &mut Dag,
    representation: &str,
    alternatives: &[String],
    methods: &[String],
    functions: &[String],
) {
    d.node(Node {
        id: "sim/sound".into(),
        kind: "simulator-soundness".into(),
        status: "open".into(),
        statement: Some(format!("the linked P-calls program over the {representation} simulator is a sound simulator (SoundSim / CoreSim.sound)")),
        ..Default::default()
    });
    let mut pieces: Vec<String> = methods.iter().map(|m| format!("method/{m}")).collect();
    pieces.extend(functions.iter().map(|f| format!("tv/{f}")));
    d.edge(
        "sim/sound",
        pieces,
        "Task: P-calls soundness from method soundness and translation validity",
        "task",
        "",
    );
    for alt in alternatives {
        let s = format!("sim/sound[{alt}]");
        let r = format!("refine/{representation}-{alt}");
        d.node(Node {
            id: s.clone(),
            kind: "simulator-soundness".into(),
            status: "open".into(),
            ..Default::default()
        });
        d.node(Node {
            id: r.clone(),
            kind: "wasm-piece".into(),
            status: "open".into(),
            statement: Some(format!("the {representation} and {alt} representations are related by a map commuting with runs and the representation relation (SimRefines)")),
            lean: Some("Silmaril.Sim.Reduce.SimRefines".into()),
            solvers: vec!["Wasm equivalence per method (G ≡ M)".into(), "lockstep difftest".into()],
            ..Default::default()
        });
        d.edge(
            "sim/sound",
            vec![s, r],
            "Silmaril.Sim.Reduce.SoundSim.ofRefines",
            "proved",
            "",
        );
    }
}
