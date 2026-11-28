# Program Expression Graphs and Peggy

The typed PEG core represents finite **Program Expression Graphs** with
sharing, branching and loop feedback. Peggy is the optimizer that uses PEGs
and adds equivalences to build E-PEGs. The current library covers graph
construction, scope and structural guards. The
[guarded Figure 11 denotation](peg-semantics.md) interprets graphs with
well-founded demands. The [checked Egg bridge](peggy-egg.md) proves
equality of native observations for ranked loop-free PEGs. The
[cyclic E-PEG certificate kernel](peggy-epeg.md) checks finite class and
candidate admission conditions and uses semantic evidence for merges
and extraction. The [finite saturation algorithm](peggy-saturation.md)
closes a supplied table of ground obligations and checks a cyclic
selection with structural row evidence. The
[bounded root optimizer](peggy-optimizer.md) matches supplied schemas,
generates and checks single-result PEG candidates, and selects by an
explicit static metric. The
[contextual optimizer](peggy-contextual-optimizer.md) rewrites shared
internal rows across ordered outputs and counts distinct reachable
application vertices.

Ross Tate, Michael Stepp, Zachary Tatlock and Sorin Lerner, *Equality
Saturation: A New Approach to Optimization*, LMCS 7(1:10), 2011,
arXiv:1012.1802v3. The versioned PDF has SHA-256
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.
Locators below use PDF page numbers. [Paper](https://arxiv.org/pdf/1012.1802v3) ·
[Journal](https://lmcs.episciences.org/1016)

The [paper coverage and reproduction map](peggy-coverage.md) also tracks the
SIMPLE pipeline, institution bridges, and open claims.

## Library boundary

| Header | Interface |
| --- | --- |
| [PEG.Defs](../../Silmaril/SSA/PEG/Defs.lean) | `InstructionSet` indexes primitives by ordered operand types and one result type. `Label` fixes the profiles of parameter, φ, θ, eval and pass nodes. A `Graph` numbers vertices independently of dependency order and uses typed references for operands and roots. The same reference can occur multiple times. A loop parent table distinguishes siblings at the same depth. |
| [PEG.Builder](../../Silmaril/SSA/PEG/Builder.lean) | Construct a table directly with `Node.ofLabel`, or use `RawGraph.check` to check numeric references, operand and root arities, and declared result sorts. Raw labels already carry their instruction profiles and typed parameter slots. The checker permits forward references and feedback and examines every row, including unreachable ones. |
| [PEG.Scope](../../Silmaril/SSA/PEG/Scope.lean) | Walks track dependency roles. `PaperWellFormed` models the three printed clauses in the ancestry order of a finite loop forest. `WellFormed` strengthens the third clause. These are certificate predicates on the whole graph. |
| [PEG.Thms](../../Silmaril/SSA/PEG/Thms.lean) | Checked wiring round trip, preservation of operand slots and edge roles under relabelling, and preservation and reflection of structural admission under opcode maps, vertex/loop reindexing and output changes. Walk lemmas let a client prove reachability invariants with local edge facts or rule out cycles by a strict rank. |

The graph indices bound all references and loop identities. Types and
numbering are distinct from structure. Graph admission uses `WellFormed`
in addition to acceptance by the wiring checker. The graph core leaves
instruction meaning to an interpretation. The guarded denotation uses
well-founded demands on node/iteration-index pairs. An arbitrary sampled
index and the monotonization prefix both contribute evaluation demands.
[Semantics](peg-semantics.md)

## The printed loop guard

Definition 5.1 on p. 23 requires a θ **node** of a strictly enclosing loop on
every cycle through eval or pass. To witness the presence of a θ on a cycle,
the cycle may take either its initial or its feedback edge. The separate
first clause still requires a feedback edge somewhere on every cycle.
`OuterFeedbackCycles` requires that the enclosing θ contributes its
feedback edge to the cycle. `WellFormed.toPaper` checks the implication
from the stronger guard to the printed one.

Consider two ordered loop identifiers `o < l`, with nullary count
instructions for 0 and 1, and the graph

```
A = θ_o(E, 0)
E = eval_l(B, 1)
B = θ_l(0, A)
```

The only simple cycle takes A's initial edge, E's first edge and B's feedback
edge. In particular, the paths from the outer θ to the inner θ cross the
inner eval's first edge. The outer θ occurs on the cycle without decreasing
the outer iteration index. The Lean fixture proves all three printed
clauses for this graph, and proves that the stronger guard rejects it.

With Fig. 11's equations, at outer index 0 let A be any fixed defined count
`k` for all inner indices. Let A be 0 at positive outer indices. B is 0 at
inner index 0 and equals A at the immediately preceding inner index
otherwise. In eval at 1 the only earlier prefix value checked is B at
inner index 0, which is defined. Thus E equals A. The fixture proves the
specialized equations for every pair of indices and exhibits two different
solutions at `(0, 0)`. This is a counterexample to Theorem 1 under the
literal printed hypotheses, already for a two-element total order. The
[guarded denotation](peg-semantics.md) proves that the stronger structural
guard makes the evaluation demands well founded. [Definition 5.1 and Fig. 11](https://arxiv.org/pdf/1012.1802v3#page=23) ·
[Lean fixture](../../tests/ssa/PEG.lean)

## Checked loop-free reversion

[Simple.Revert.Thms](../../Silmaril/SSA/PEG/Simple/Revert/Thms.lean) admits typed,
single-result PEGs with zero loops. The manual certificate path calls
`Certificate.check g rank plan` on a typed graph, optionally obtained with
`RawGraph.check`. The rank must strictly decrease along every operand edge,
including edges in dead rows. Vertex identities need no particular numbering.
For this fragment, typed references supply Fig. 19's parameter, instruction,
φ and root types. `Certificate.depthZero` uses the checked rank to derive
the recursive operand premises at depth zero with an empty assumption context.

A plan starts with the return root demanded. A `reveal i` hint can expose the
strict operands of a demanded operation or the guard of a demanded φ. Each
`bind` needs demand evidence and local slots for all operands. A `branch`
needs a demanded φ and a previously bound guard. Its two subplans inherit the
entry locals and may use the demand for their respective selected operands.
Each projects to its selected value and the original entry locals. The
continuation receives the joined φ value and those entry locals. The checker
requires one writer site per scheduled vertex across the entire plan. This
lets a dominating binding serve repeated wires and survive a branch join.
The restriction rejects some valid loop-free graphs and placements, including
cases that would need to duplicate a vertex across disjoint arms or justify
moving it with stronger demand information.
[Certificate and lowering](../../Silmaril/SSA/PEG/Simple/Revert/Defs.lean)

### Automatic scheduling

`Automatic.check g` computes a candidate rank by propagating dependency
heights through a finite table, then synthesizes the schedule. Use
`Automatic.checkRanked g rank` when a graph producer already has a rank.
Each scope scans vertices from higher to lower rank, exposing the strict
operands of demanded nodes. It emits bindings in the reverse order. A φ
recursively schedules each selected operand with the locals available at
the branch. A shared budget of one writer per vertex bounds generation.
The existing certificate checker validates the generated plan, including
the whole-table rank and unique writer sites.
[`Automatic.Defs`](../../Silmaril/SSA/PEG/Simple/Revert/Automatic/Defs.lean)

`inferRank_ordered` proves that inference succeeds whenever a valid rank
exists. `check_accepts_straightLine` proves that the graph-only entry point
admits every such graph with only parameter and primitive rows. Arbitrary vertex
numbering, dead rows and repeated wires are allowed. For graphs with φ,
the planner conservatively rejects placements that would bind a vertex
in more than one scope. Scope placement is determined by rank order, so
some graphs with legal manual schedules can also be rejected. The planner
uses strict dependency discovery within each scope. Cross-arm demand
analysis and the paper's full MustEval progress obligations remain open.
[Acceptance theorem](../../Silmaril/SSA/PEG/Simple/Revert/Automatic/Thms.lean)

The output is the existing `Simple.Program P false params result` and runs
using `Program.runLoopFree`, which realizes the existing `Exec` relation.
`Certificate.revert_returns` and `Certificate.revert_run` preserve every
defined Fig. 11 root observation for the same typed input and interpretation.
The model can return bottom for primitive calls. Purity comes from the
value-only interpretation, and the checker justifies every scheduled
computation on a successful path. The result observes the returned value.
Failure correspondence, divergence and effects remain outside this theorem.
[Correctness](../../Silmaril/SSA/PEG/Simple/Revert/Thms.lean)

The relation to [#3316](https://github.com/hiloopai/silmaril-lean/pull/3316)
is via the common Fig. 11 observation. Its `observeCFG_peg` proves the
total-model λRTL/flat-CFG path with eager value-selects and a store frame.
That theorem applies unchanged on the common total fragment. Here, a φ
emits a SIMPLE branch and the unselected arm may be undefined. The proof
uses the existing `Graph.denote_solves` and rank soundness API from #3253
and the SIMPLE execution API from #3306. Equational E-PEG certificates concern
the denotation of equal representatives. Reversion admission applies to a
chosen representative and its schedule.

| Paper obligation | Status |
| --- | --- |
| [Fig. 19 and §7.1](https://arxiv.org/pdf/1012.1802v3#page=41) | Typed row derivations and a bounded checker with explicit printed and inward eval/pass premises. Every typed structured SIMPLE compilation has an inward derivation at the checker's inferred depths. The bridge checks an independent demand rank for Figure 11 observations. Search completeness and the implication to Definition 5.1 remain open. [Clause correspondence](peggy-coverage.md#figure-19-typing-and-the-semantic-gate) |
| [§§7.2–7.5](https://arxiv.org/pdf/1012.1802v3#page=41) | Automatic plan synthesis, one-result scope placement and sequencing for the admitted fragment. General branch-region extraction and multi-result joins remain open. Loop extraction must relate θ initialization and simultaneous feedback copies, first defined pass, and eval's earlier-prefix demands to the emitted loop. |
| [§§7.6–7.7](https://arxiv.org/pdf/1012.1802v3#page=49) | Loop and branch fusion remain open. Fusion must preserve exit predicates, feedback dependencies and demands under the chosen observation. |
| [§7.8](https://arxiv.org/pdf/1012.1802v3#page=53) | Checked local hints use the strict operation and φ-guard rules. A computed MustEval analysis with Definition 7's progress requirements, statement/loop contexts and automatic redundancy hoisting remains open. |
| [§7.9](https://arxiv.org/pdf/1012.1802v3#page=56) | LICM remains open. Invariance and demand on entry need separate justification, including zero-iteration and partial-operation cases. |

Run `make check CHECK_TARGETS='+Silmaril.SSA.PEG.Simple.Revert.Automatic.Thms PEGCoreTests'`
for the scoped build and repository gates. The
[fixture](../../tests/ssa/PEGRevert.lean) runs both φ choices, checks a
bottom unselected arm and a dominating shared value, and exercises rejected
speculation, scope, duplicate-binding and rank certificates. It also checks
automatic admission and runs the synthesized syntax.

## Checked SIMPLE optimization

The executable SIMPLE pipeline combines frontend lowering, contextual
discovery and replay, and automatic reversion. It preserves successful
SIMPLE returns under rule laws over partial values. The worked example
optimizes a shared computation inside a φ arm and executes the emitted
SIMPLE. [Pipeline contract and example](peggy-simple-validation.md)

## Follow-up roadmap

This is the original dependency plan. See the
[coverage map's remaining work](peggy-coverage.md#remaining-work-in-priority-order)
for the current priorities.

1. **PEG invariants and rule schemas**. Extend the
   [guarded semantics](peg-semantics.md) with alpha and parameter transport,
   sound syntactic invariance, and reusable rule schemas with proofs of
   their conditions for bottom, overflow and partial operations. For
   example, deleting `φ(c,a,a)` needs a defined guard when `a` is defined.
2. **Dialect institution**. Add `Silmaril.SSA.Peggy.Dialect` and
   `.Institution`. Dialect arrows map symbols forward at fixed profiles.
   Sentences compare typed open graphs at a shared boundary and loop frame.
   Start with discrete models. Reducts precompose symbol interpretations,
   so evaluation after relabelling must equal evaluation in the reduct.
   Prove identity, composition and
   `M ⊨ map f e ↔ reduct f M ⊨ e` using the
   [institution builders](../../Silmaril/Logic/Inst/Builders/Core/Defs.lean).
   Typed program substitution for instruction lowerings needs its own
   interpretation and strictness laws.
3. **SIMPLE and reversion**. Extend the loop-free Fig. 15/17 frontend and
   depth-zero reversion to loop syntax. Dropped divergence or faults require
   a threaded observation token and a separate adequacy theorem. Keep demands
   for earlier samples or prove prefix definedness. Stage loop extraction
   and automatic branch extraction before fusion, MustEval and LICM.
   The authors' Coq `preserveFunctioner` is a proof guide for their
   structured SIMPLER syntax. Its published evaluator samples eval's
   chosen index directly, so correspondence with Fig. 11 needs a proof.
   [Coq sources](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/)
4. **E-PEGs and optimization**. The [E-PEG certificate kernel](peggy-epeg.md)
   proves stream equality for same-label congruence and merges with
   independently justified laws. It checks the demand rank and root
   classes of a proposed extraction. The
   [finite worklist](peggy-saturation.md) proves least closure and
   order independence for a fixed table of ground reasons. It derives
   candidate equations for same-label rewiring. The
   [root optimizer](peggy-optimizer.md) adds rows and finds typed
   instances in a bounded loop-free search. The
   [cyclic optimizer](peggy-cyclic-optimizer.md) discovers guarded θ
   self-feedback and checks the compacted candidate on a one-loop profile.
   Extend matching and node
   generation to more general contexts, and prove reversion. The
   [acyclic bridge](peggy-egg.md) reuses sorted Egg replay. The full
   node-generating form of §4 remains a separate proof obligation. Use an independent graph and
   CFG-like check on extracted representatives. The displayed Boolean
   constraints in §8.3 also admit invalid selections, such as a θ
   initializer selecting its own class. Prove reversion correctness
   separately from any cost-minimality claim. Prove validation by
   composition with adequate frontends at the chosen observation.
5. **IR bridges**. Put `Bridge.Egg`, `Bridge.MLIR` and `Bridge.RVSDG`
   under `Silmaril.SSA.Peggy`. The [Egg bridge](peggy-egg.md) checks acyclic
   unfolding and equality of ordered Figure 11 observations. Start the
   MLIR and RVSDG bridges with pure total acyclic PEGs and regionless MLIR/ordered
   RVSDG values. For structured RVSDG loops, align θ body iterations, exit
   polarity, and PEG pass/eval.
   Compose typed λSSA and the pure Sea of Nodes diamond through RVSDG.
   Use typed, coherently versioned λRTL forward CFGs with an explicit
   exit/store observation. Put machine RTL and Wasm adapters in their own
   regions with their memory, oracle, trapping and divergence hypotheses.
   Use comorphisms for forward sentence translations and model pullbacks
   with naturality and exact satisfaction. A morphism with the same
   signature direction needs sentences backward and models forward.
   A one-way compiler theorem supplies simulation or refinement. Exact
   satisfaction and consequence reflection require separate proofs,
   with model expansiveness for reflection. [RVSDG–MLIR model bridge](rvsdg/mlir/rvsdg-mlir-regionless.md) ·
   [SSA and machine boundaries](ssa.md)
6. **Paper view and Java profile**. Add a leaf under
   `Silmaril.Papers.TateSteppTatlockLerner2011` once the reusable theorems
   exist. Register proved institutional edges in the logic graph. Develop
   Java call, heap and exception semantics and a checked partial heap
   linearizer independently. General CFG conversion uses the paper's
   separate reference [50]. Historical reproduction needs pinned Peggy,
   Soot, solver, JVM, benchmarks and machine.

The first two steps depend on the core. SIMPLE and the institution can proceed
independently once the relevant semantic profile is proved. Merge replay can
precede reversion. End-to-end optimization needs both, with matched
observations. SSA may import Prelude, Semantics and Logic under
[regions.toml](../../regions.toml). The
[Formats e-graph snapshot](../guarded-egraph.md) is an architecture reference
from a different region. Sharing executable code with it would require
an independently reviewed promotion of its format-independent core.

## Paper coverage

See the [paper coverage and reproduction map](peggy-coverage.md) for the
current theorem, implementation and experiment coverage by paper section.

## Check the core

```sh
lake build --wfail +Silmaril.SSA.PEG.Thms PEGCoreTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEG.lean
lake env leanchecker Silmaril.SSA.PEG.Thms
scripts/check-layout.sh
```

`PEGCoreTests` is part of `make check`. The fixture checks repeated operand
and root references, rejects invalid wiring, checks a dialect symbol
identification and a simultaneous loop/vertex permutation, and checks both
versions of the loop guard through the public headers.
