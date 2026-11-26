# Peggy paper coverage and reproduction

Silmaril proves the repaired Figure 11 denotation and structured SIMPLE
forward preservation. It checks selected cyclic rewrites and reverts some
single- and two-level loops. A worked replay goes from Figure 6(b) to
executable SIMPLE. Reversion for arbitrary structured graphs, the full
Peggy engine and the historical Java experiments remain open.

The reference is Ross Tate, Michael Stepp, Zachary Tatlock and Sorin Lerner,
*Equality Saturation: A New Approach to Optimization*, LMCS 7(1:10), 2011,
arXiv:1012.1802v3, 80 PDF pages. SHA-256 of the PDF is
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.
Page links use PDF page numbers. PEG denotes **Program Expression Graph**.
[Paper](https://arxiv.org/pdf/1012.1802v3) · [Journal](https://lmcs.episciences.org/1016)

**Proved** refers to the stated Lean theorem under its listed hypotheses.
**Implemented** refers to executable code or fixtures with their stated
acceptance boundary. **Open** marks outstanding work. This map records
declarations on the audited main revision. PR links identify where each
result landed. Module names omit `Silmaril.SSA.` where clear.
[Audited main commit](https://github.com/hiloopai/silmaril-lean/tree/f3286c67dbdbe495b67d54c13dfd2722277e2240)

## Graphs, forward translation and examples

| Paper locator | Coverage in Lean | Open or different |
| --- | --- | --- |
| §§1–3, worked optimizations | **Implemented and checked examples.** `tests/ssa/PEG.lean` exercises typed sharing, lazy branching and loop feedback. `tests/ssa/PEGSimple.lean` checks factorial and later sibling, branch-contained and nested loops. Selected rules and bounded optimization have independent fixtures. [Paper](https://arxiv.org/pdf/1012.1802v3#page=2) · [#3205](https://github.com/hiloopai/silmaril-lean/pull/3205) · [#3335](https://github.com/hiloopai/silmaril-lean/pull/3335) · [#3375](https://github.com/hiloopai/silmaril-lean/pull/3375) | Figure 6(b–d) now has a checked replay and executable SIMPLE counterpart below. The broader worked examples, including §2.3 inter-loop strength reduction and §3.4 branch hoisting, remain open. |
| §5.1, Fig. 11, Def. 5.1 and Thm. 1 | **Implemented** typed, numbered graphs in `PEG.Defs` and wiring checks in `RawGraph.check` in `PEG.Builder`. **Proved** structural and demand lemmas in `PEG.Thms` and `PEG.Semantics.Thms`, including `Graph.existsUnique_solves_of_wellFormed`, `Graph.demandWellFounded_of_check` and `Graph.observe_denote_mapOps`. [Graph definitions](../../Silmaril/SSA/PEG/Defs.lean) · [Denotation proofs](../../Silmaril/SSA/PEG/Semantics/Thms.lean) · [#3205](https://github.com/hiloopai/silmaril-lean/pull/3205) · [#3253](https://github.com/hiloopai/silmaril-lean/pull/3253) | Lean's structural guard strengthens the printed guard. See the discrepancy below. |
| §5.3, Def. 5.2 and Appendix A | **Proved** the largest syntactic invariance predicate and its semantic consequence in `PEG.Rules.Thms` (`invariantAt_largest`, `denote_invariant`), plus guarded rules including `phi_same_of_defined`, `theta_self`, `eval_invariant` and `pass_peel`. [Rules](../../Silmaril/SSA/PEG/Rules/Thms.lean) · [#3358](https://github.com/hiloopai/silmaril-lean/pull/3358) | Open: the remaining discharge conditions and rules for the paper's partial-stream and language-specific examples. For example, `φ(c,a,a) = a` needs a defined condition for the Lean rule. Appendix A itself lists only rules relevant to Fig. 38, a subset of the historical engine's rules. |
| §6, Figs. 15 and 17, Thm. 2 | **Implemented** typed positional variables, primitive applications, fresh assignments, context projection, sequence, branches, while and one return. **Proved** `Program.translate_returns` in `PEG.Simple.Thms` (loop-free), `WhileProgram.translate_returns` in `PEG.Simple.While.Thms` (top-level while), and `translate_returns` in `PEG.Simple.Structured.Thms` (compositional loops). The structured compiler derives first exits and defined eval prefixes from finite source execution at fixed enclosing coordinates. It requires the supplied Boolean negation opcode to implement negation. `Structured.translate_wellFormed` proves the emitted graph itself meets Peggy's structural sentence admission. [Structured proofs](../../Silmaril/SSA/PEG/Simple/Structured/Thms.lean) · [#3306](https://github.com/hiloopai/silmaril-lean/pull/3306) · [#3335](https://github.com/hiloopai/silmaril-lean/pull/3335) · [#3375](https://github.com/hiloopai/silmaril-lean/pull/3375) · [#3427](https://github.com/hiloopai/silmaril-lean/pull/3427) | Successful source return implies the same defined PEG result (the structured theorem holds at every output index, including the paper's all-zero index). Failure and divergence are outside that implication. |

### Theorem 1 guard and observation

Definition 5.1(3) asks for a strictly enclosing θ **node** on each cycle
through an eval or pass. Take enclosing loop `o`, inner loop `l` and
`A = θ_o(E,0)`, `E = eval_l(B,1)`, `B = θ_l(0,A)`. The cycle uses A's
initial edge and B's feedback edge. The fixture checks all three printed
clauses and exhibits two solutions of the specialized Figure 11 equations
that disagree at index `(0,0)`. It also checks the cycle of actual demands.
`Graph.WellFormed` requires the strictly enclosing θ's **feedback edge**.
For this stronger guard the demand relation is well founded even with
arbitrary sample indices and all earlier eval-prefix indices. The unique
simultaneous solution uses lazy φ, θ's initial/previous feedback selection,
least eligible pass, and eval's defined-prefix check. The rank checker gives
a separate sufficient demand certificate. Relabelling preserves exact
observations, including bottom, under model reduct.
[Fig. 11 and Def. 5.1](https://arxiv.org/pdf/1012.1802v3#page=23) ·
[Thm. 1](https://arxiv.org/pdf/1012.1802v3#page=24) · [Fixture](../../tests/ssa/PEG.lean) · [Semantics](peg-semantics.md)

### Theorem 2 and completion

The paper already limits Theorem 2 to successful returns and explains the
discarded infinite-loop case. The Lean source `Exec` distinguishes finite
primitive failure from divergence (absence of a finite execution). A PEG
root has one bottom, and it can also be defined despite source failure in
an assignment outside the return's demanded dependencies. The loop-free
fixture checks the latter. Section 6's Figure 18 completion/effect-token
encoding has no delivered Lean preservation theorem here. The authors'
Coq `PEGSem.v` samples eval's selected index directly. Lean uses the
Figure 11 defined-prefix rule, so an undefined earlier sample can prevent
a defined later sample from being observed.
[Thm. 2 and Fig. 18](https://arxiv.org/pdf/1012.1802v3#page=36) ·
[Coq source](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/PEGSem.v) ·
[Source semantics and comparison](peg-simple.md#comparison-with-the-authors-coq)

## Figure 19 and cyclic reversion (§7)

### Figure 19 typing and the semantic gate

Figure 19's printed Type-Eval-Pass premise is `surrounding = sampled + 1`.
`CFGContext.printed_no_root_eval` proves that a directly designated eval
cannot type at depth zero under that premise. Lean keeps the literal
`.printed` convention and a separate `.inward` convention
(`sampled = surrounding + 1`) for a parent sampling an immediate child.
The fused eval/pass rule checks the same loop identity and the
assumption-depth condition. `Figure19.check` searches for root
derivations with bounded fuel and a checked forest depth map.
`checkGuarded` also checks a whole-table demand rank.
`Simple.Structured.translate_figure19` proves an inward derivation at
the checker's inferred depths for **every** structured compilation.
`Figure19.Structured.check_isSome` reduces the compiler's executable
admission to the bounded typing search. A sufficient fuel bound for every compiler output and general search
completeness remain open. Typing the designated roots and proving whole-table
Definition 5.1 legality are separate obligations for an arbitrary graph.
[Fig. 19](https://arxiv.org/pdf/1012.1802v3#page=41) ·
[Checker](../../Silmaril/SSA/PEG/Figure19/Defs.lean) ·
[Boundary theorem](../../Silmaril/SSA/PEG/Figure19/Thms.lean) ·
[Compiler theorem](../../Silmaril/SSA/PEG/Simple/Structured/Figure19/Thms.lean) ·
[Checked compiler interface](../../Silmaril/SSA/PEG/Figure19/Structured/Thms.lean) ·
[#3986](https://github.com/hiloopai/silmaril-lean/pull/3986) ·
[#4010](https://github.com/hiloopai/silmaril-lean/pull/4010)

| Figure 19 rules | Lean judgment |
| --- | --- |
| Type-PEG-Context, Type-PEG | `CFGContext` checks each ordered designated root at depth zero with no assumptions. |
| Type-Param, Type-Op, Type-Phi | Typed parameter ports and ordered primitive operand profiles. Both φ arms and the Boolean flag derive at the current depth and under the current assumptions. |
| Type-Theta, Type-Assume | The initializer derives at the preceding depth. The feedback derives with the exact θ row and its depth added to the assumption context. A matching assumption can close a θ derivation. |
| Type-Eval-Pass, Type-Reduce | The value and same-loop pass predicate derive at the sampled depth. Retained assumptions must be strictly shallower. Reduction allows a lower depth bound and fewer assumptions. |

| Fragment | Executable entry and proved scope |
| --- | --- |
| Loop-free | `PEG.Simple.Revert.Automatic.check` infers a rank and schedule. `checkRanked_accepts_straightLine` covers ranked straight-line graphs. For checked schedules, `Certificate.revert_returns` and `revert_run` relate a defined PEG root to successful SIMPLE execution. Sharing can still make automatic placement reject. [Proofs](../../Silmaril/SSA/PEG/Simple/Revert/Thms.lean) · [Automatic proofs](../../Silmaril/SSA/PEG/Simple/Revert/Automatic/Thms.lean) · [#3348](https://github.com/hiloopai/silmaril-lean/pull/3348) · [#3388](https://github.com/hiloopai/silmaril-lean/pull/3388) |
| One loop, scalar or carried vector | The exact scalar and pair extractors check recompilation. `While.Region.Automatic.extract g` infers the descriptor, rank and schedules for a single loop with an ordered typed carried vector and one sampled return. `extract_accepts` assumes a wired, schedulable boundary, one unique θ per initializer port and a bounded rank in the fixed eval/pass phase layout. `Region.Certificate.returns_iff_observe` takes guard and whole-update totality and the negation law. `runFuel_of_defined` witnesses fuel equal to the pass count. [Region proofs](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Thms.lean) · [Inference proofs](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Automatic/Thms.lean) · [#3389](https://github.com/hiloopai/silmaril-lean/pull/3389) · [#3441](https://github.com/hiloopai/silmaril-lean/pull/3441) · [#3703](https://github.com/hiloopai/silmaril-lean/pull/3703) · [#3725](https://github.com/hiloopai/silmaril-lean/pull/3725) |
| Two-level nesting | `While.Nested.Reindexed.Automatic.extract` infers a form and row/loop permutations and checks exact recompilation. The form has one child per continuing outer iteration, explicit typed captures, a loop-free inner step and a loop-free outer commit. `Accepted.returns_iff_observe` uses guard totality, successful child termination on continuing captures, successful commit and negation. `While.Nested.Projected.extract` first projects to the operand closure of the return and loop-bundle evals, with the correspondence to the original graph also requiring its demand well-foundedness. Arbitrary nested/branched source compilation already works. Extraction of arbitrary such graphs remains open. [Form](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Defs.lean) · [Reindexing proof](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Reindexed/Automatic/Thms.lean) · [Projection proof](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Projected/Thms.lean) · [#3760](https://github.com/hiloopai/silmaril-lean/pull/3760) · [#3794](https://github.com/hiloopai/silmaril-lean/pull/3794) · [#3866](https://github.com/hiloopai/silmaril-lean/pull/3866) · [#3893](https://github.com/hiloopai/silmaril-lean/pull/3893) |
| Placement (§§7.8–7.9) | `Region.Placement.extract` checks one shared computation on strict paths in a lazy feedback branch. `Figure19.MustEval.analyze` computes a bounded, same-index must-demand table with `defined` soundness and `stable` under a local rank. `Region.Placement.MustEval.extract` uses it for one checked shared placement. `Region.Hoist.check` handles one invariant with first-trip caching, using both defined demand and invariance. `Accepted.preserves` starts from a successful reference return, including zero trips. General Definition 7 precision, hoisting and LICM, loop/branch fusion and general CFG reversion remain open. [Placement](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Placement/Thms.lean) · [MustEval](../../Silmaril/SSA/PEG/Figure19/Placement/MustEval/Thms.lean) · [MustEval reversion](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Placement/MustEval/Thms.lean) · [Hoist](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Hoist/Thms.lean) · [#4059](https://github.com/hiloopai/silmaril-lean/pull/4059) · [#4076](https://github.com/hiloopai/silmaril-lean/pull/4076) · [#4107](https://github.com/hiloopai/silmaril-lean/pull/4107) |

### Graph-local parent/child schedules

`Nested.Region.check` takes a typed descriptor and demand rank for one
parentless loop and one immediate child. It checks the parent links,
ordered θ initializers and feedback, the shared pass within each loop,
the child's eval bundle, and the designated outer eval. Outer
initializers match typed input ports. The primitive scheduler checks
the outer exit test over the old outer θ vector, the child initializer
over that same vector, the child test and feedback over the child θ
vector plus the retained outer values, and the outer commit over the
child exit bundle plus the old outer values. The check uses the supplied
rows directly and permits independent numbering of rows and loop keys.

The emitted outer body builds a fresh child store before its inner
`while`. `Accepted.activation_observation` fixes the enclosing coordinates,
starts the child's θ streams at zero, and derives one least child pass
and the defined eval prefix from the finite child trace. Its returned
store realizes both the child evals and the retained outer captures at
the caller's index. The outer proof establishes the capture premise
uniformly at each outer iteration, invokes the child theorem, and
replays the entire simultaneous commit. `Accepted.observe_of_returns`
then relates an actual successful nested SIMPLE return to Figure 11.
The checked demand rank supplies the valuation, the negation law connects
the tests, and the successful trace supplies primitive definedness and
child termination. Returning from a PEG exit alone remains open for
this adapter. It requires a way to obtain each continuing activation's
child exit and the full commit's definedness.

The regression uses a hand-wired graph with 16 rows and two loop keys.
Its first two child activations take two and one steps and commit
accumulators 3 and 4. A well-ranked initializer that reads the original
parameter in place of the current outer θ is rejected by the slice
checker. A mismatched child pass is also rejected. The result covers
the supplied two-level primitive shape. Boundary discovery, arbitrary
nesting, and effects remain open for this adapter.
[Graph-local checker](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Defs.lean) ·
[Activation and return theorems](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Thms.lean) ·
[Regression fixture](../../tests/ssa/PEGCanonicalWhile.lean)

## Saturation, selection and worked optimization

### Section 4 and the saturation engine

| Paper claim | Proved or implemented boundary |
| --- | --- |
| (4.1) and (4.2) | `NormalForms.Inflationary` says each analysis step extends its source. `MonotoneSimulation` says that after enlarging the source, the **same analysis** has a step whose result covers the smaller step's result. A simulated step may stutter. For concrete E-PEG append receipts, `Step.embedding` proves (4.1). The comparison uses typed injections preserving rows, ordered roots, forest and old class equalities. `ZeroSampleAnalysis.inflationary` and `ZeroSampleAnalysis.monotone` verify both assumptions for fresh zero-sample generation. [Abstract definitions](../../Silmaril/SSA/Peggy/EPEG/Saturation/NormalForms/Defs.lean) · [Concrete proofs](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Comparison/Thms.lean) · [#4072](https://github.com/hiloopai/silmaril-lean/pull/4072) · [#4096](https://github.com/hiloopai/silmaril-lean/pull/4096) |
| (4.3) and (4.4) | `NormalForms.delayed_step` needs simulation of the delayed analysis and inflationarity of the intervening analysis. `stableNormalForm_least` and `stableNormalForm_unique` assume a reflexive, transitive comparison and inflationarity plus simulation for **every** family member. Every step out of a stable state is covered by that state. Two reachable stable states mutually compare. `paperNormalForm_unique` additionally assumes antisymmetry and proves literal equality for the paper's identity-filtered terminal forms. The E-PEG embedding corollary gives mutual embeddings. These are conditional uniqueness results. `ZeroSample.no_stable` shows that fresh appending from a matched site leaves strict progress in every reachable state. [Abstract proofs](../../Silmaril/SSA/Peggy/EPEG/Saturation/NormalForms/Thms.lean) · [E-PEG specialization](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Comparison/Thms.lean) · [§4](https://arxiv.org/pdf/1012.1802v3#page=19) · [#4111](https://github.com/hiloopai/silmaril-lean/pull/4111) |
| Executable closure (§8.2) | `Saturation.saturate` closes a supplied finite table of ground obligations. `saturate_least`, `saturate_perm` and `run_denote_sound` cover that fixed table, with semantic validity of rule obligations. `Extension.Plan.run` replays a supplied prefix that appends typed rows, with soundness under the corresponding receipt laws. `Extension.Dedup.close` reuses or appends the exact zero-sample RHS for a caller-supplied site list. `close_checked` requires initial eligibility, `close_fixed` proves re-running a checked closed scope stutters, and `close_sound` uses the zero law. A worklist that discovers all new redexes and a Rete implementation/refinement for a substantial analysis family remain open. [Fixed table](../../Silmaril/SSA/Peggy/EPEG/Saturation/Thms.lean) · [Append replay](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Thms.lean) · [Scoped closure](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Dedup/Thms.lean) · [#3313](https://github.com/hiloopai/silmaril-lean/pull/3313) · [#4138](https://github.com/hiloopai/silmaril-lean/pull/4138) |

### Selection cycle legality

- Sorted Egg replay for ranked acyclic PEGs is connected to Figure 11 by
  `checkOutputs_figure11_sound`. For cyclic candidates,
  `EPEG.Selection.observe_sound_of_rows` uses checked row evidence,
  valid classes and native demand ranks. The printed §8.3 reachability
  clauses exclude cycles of selected non-θ rows. A θ initializer
  self-cycle passes those clauses and violates Definition 5.1(1).
  `FeedbackRank.infer` checks a strict rank on nonfeedback edges.
  `FeedbackRank.feedbackCycles` proves clause (1). Scope and enclosing
  observer feedback, Figure 19, and demand well-foundedness have their own
  gates. `Optimizer.Cyclic.Match.Replay.feedbackCycles` exposes the
  wired candidate's legality alongside `Match.Replay.sound` for its
  observation. [Egg bridge](../../Silmaril/SSA/Peggy/Bridge/Figure11/Thms.lean) ·
  [Selection soundness](../../Silmaril/SSA/Peggy/EPEG/Selection/Thms.lean) ·
  [Legality](../../Silmaril/SSA/Peggy/EPEG/Selection/Legality/Thms.lean) ·
  [§8.3](https://arxiv.org/pdf/1012.1802v3#page=64) ·
  [#3284](https://github.com/hiloopai/silmaril-lean/pull/3284) ·
  [#4129](https://github.com/hiloopai/silmaril-lean/pull/4129)
### Discovery and profitability (§§8.3–8.4)

- Bounded single-root and contextual acyclic discovery have checked
  candidates. `Optimizer.Contextual.optimize_min` minimizes distinct
  reachable primitive and φ rows among the explored candidates. The
  original cyclic `Optimizer.Cyclic.optimize` recognizes a single-loop
  self-feedback θ with a leaf initializer in a profile excluding eval/pass.
  `SimpleValidation.Cyclic.optimize` uses checked row replay and region
  reversion for a single sampled return, including graphs using eval/pass.
  `Cyclic.Source.optimize` starts
  from a typed top-level `WhileProgram`; `Accepted.returns` uses the
  reverter's full-step totality and negation. General cyclic discovery,
  the paper's weighted pseudo-Boolean cost, and a verified solver/extractor
  with CFG-like legality and optimality remain open. Figure 11's separate
  pass and eval already let compiler output share one exit index across
  carried samples. [Contextual proof](../../Silmaril/SSA/Peggy/Optimizer/Contextual/Thms.lean) ·
  [Cyclic replay](../../Silmaril/SSA/Peggy/Optimizer/Cyclic/Thms.lean) ·
  [Cyclic validation](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Thms.lean) ·
  [Source pipeline](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Source/Thms.lean) ·
  [#3346](https://github.com/hiloopai/silmaril-lean/pull/3346) ·
  [#3372](https://github.com/hiloopai/silmaril-lean/pull/3372) ·
  [#3626](https://github.com/hiloopai/silmaril-lean/pull/3626) ·
  [#3924](https://github.com/hiloopai/silmaril-lean/pull/3924) ·
  [#3957](https://github.com/hiloopai/silmaril-lean/pull/3957)

### Figure 6(b) to executable SIMPLE

1. `Peggy.Worked.EvalScale.Match.atSite` matches Figure 6(b→c), then
   appends, merges and checks a selection. `Match.extract_sound` needs
   valid source classes, well-founded source demand, a checked candidate
   and the arithmetic law. A defined invariant factor and totality with
   that factor keep the rewrite from introducing an undefined eval prefix.
   [Code-motion theorem](../../Silmaril/SSA/Peggy/Worked/EvalScale/Thms.lean) ·
   [#4171](https://github.com/hiloopai/silmaril-lean/pull/4171)
2. `Peggy.Worked.StrengthReduction.Match.atSite` matches (c→d).
   `Match.candidate_sound` compares the actual feedback rewrite with the
   original, under an independent rank check and laws for the folded
   initializer and the step/scale equality on partial values. The worked
   rewrite replaces multiplication of the counter stream with a θ
   recurrence incremented by five. [Strength-reduction theorem](../../Silmaril/SSA/Peggy/Worked/StrengthReduction/Thms.lean) ·
   [#4199](https://github.com/hiloopai/silmaril-lean/pull/4199)
3. `PEG.Simple.Revert.While.Region.Closed.Automatic.extract` reads the
   resulting graph and the zero, unit-tick and negation opcode roles.
   It checks one parentless loop, a shared pass, a unique carried unit
   counter and primitive initializer, guard, update and exit schedules.
   The tests execute `recovered.certificate.runFuel`. The Figure 6
   fixture checks `[15, 3, 3, 15]` at fuel 3, exhaustion at fuel 2,
   ordered duplicate outputs and no multiply in the emitted SIMPLE.
   It also checks recovery after row permutation. The matcher calls for
   the two rewrites use designated sites in the worked graph.
   [Extractor](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Closed/Automatic/Defs.lean) ·
   [Fixture](../../tests/ssa/PeggyEgg.lean) ·
   [Fig. 6](https://arxiv.org/pdf/1012.1802v3#page=15) ·
   [#4241](https://github.com/hiloopai/silmaril-lean/pull/4241) ·
   [#4267](https://github.com/hiloopai/silmaril-lean/pull/4267)

The same automatic extractor accepts typed external inputs. The initializer
can read them, the guard and update can read them with the old carried vector,
and the exit can read them with evals and the shared pass. The regression
uses one graph for zero and three trips. It checks the four count outputs
`[10, 0, 6, 10]` and `[25, 3, 21, 25]` alongside a direct Boolean output.
`Recovered.observe_of_exec` proves that a successful emitted run gives the
original ordered PEG observation on the same typed input, under the role
laws.

The merged finite-return converse is executable. Given the role laws,
totality of the four checked slices (initializer, guard, full
simultaneous step, finish), a defined shared pass `some k` on the input
and a fully defined ordered observation, `Recovered.runFuel_of_firstExit`
returns exactly that tuple at fuel `k`. `Recovered.exec_iff_firstExit`
relates a successful emitted execution to existence of the first exit
and that tuple, under the same hypotheses. `Accepted.Total` is a
schedule-level condition. `Accepted.total_of_primitives` proves it when
all primitive applications are total.
The pass-only regression shows why the full update matters: the pass
and all designated roots can be defined despite a partial update in
an unobserved carried slot. The earlier
`Region.Certificate.returns_iff_observe` covers a different single-result
descriptor. Neither converse detects traps or divergence.
[Typed-input proofs](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Closed/Automatic/Thms.lean) ·
[First exit and slice totality](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Closed/Defs.lean) ·
[Total-primitive corollary](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Closed/Thms.lean) ·
[Detailed worked replay](peggy-fig6-strength-reduction.md) ·
[#4306](https://github.com/hiloopai/silmaril-lean/pull/4306) ·
[#4349](https://github.com/hiloopai/silmaril-lean/pull/4349)

## Dialects, institutions and IR bridges

The reusable `PEG` modules define graph syntax, admission and semantics.
`Peggy.Dialect` and `Peggy.Institution` build equations, satisfaction and
reducts on top. Signature arrows preserve ordered opcode profiles over
fixed sorts. `Peggy.Dialect.sentenceFunctor` maps equations forward, and
`Peggy.Dialect.Equation.holds_map` relates exact ordered partial observations
at every index in a model and its reduct. The models of `Peggy.Institution.inst`
are discrete. `familyComorphism` and `familyChange` reindex functorial
dialect families. The table distinguishes bundled institution comorphisms
(forward syntax, backward model comparison) from executable lowerings and
finite-return theorems. The ordered loop lowerings below start from a
checked, parentless, pure single-loop bundle with a common pass and typed
guard/update schedules.
[Dialect](../../Silmaril/SSA/Peggy/Dialect/Thms.lean) ·
[Institution](../../Silmaril/SSA/Peggy/Institution/Thms.lean) ·
[Dialect families](../../Silmaril/SSA/Peggy/Institution/Family/Defs.lean) ·
[#3229](https://github.com/hiloopai/silmaril-lean/pull/3229) ·
[#3380](https://github.com/hiloopai/silmaril-lean/pull/3380)

| Route | Theorem, interface and observation |
| --- | --- |
| Many-sorted equational logic → total-primitive Peggy | `Equational.comorphism`, `exact_satisfaction`, `modelExpansive` and `entails_compile_iff` give entailment equivalence in the stated total-primitive subinstitution. [Theorems](../../Silmaril/SSA/Peggy/Bridge/Equational/Thms.lean) · [#3414](https://github.com/hiloopai/silmaril-lean/pull/3414) |
| Ordered acyclic value PEG → regionless RVSDG → regionless MLIR; forward CFG and scoped λSSA diamond | The ordered, pure, total zero-loop comorphisms `peggyToRVSDG`, `rvsdgToMLIR`, `peggyToMLIR` and `peggyToMLIR_modelExpansive` live in `Peggy.Bridge.IR.Thms`. Separate program theorems are `observeCFG_peg` for typed λRTL/forward CFG and `ScopedDiamond.lower_eval_iff` for the scoped λSSA diamond. [Comorphisms](../../Silmaril/SSA/Peggy/Bridge/IR/Thms.lean) · [Forward CFG](../../Silmaril/SSA/PEG/Bridge/ForwardCFG/Thms.lean) · [Diamond](../../Silmaril/SSA/PEG/Bridge/LambdaSSA/Thms.lean) · [#3479](https://github.com/hiloopai/silmaril-lean/pull/3479) · [#3316](https://github.com/hiloopai/silmaril-lean/pull/3316) · [#3404](https://github.com/hiloopai/silmaril-lean/pull/3404) |
| Ordered checked PEG loop → numbered RVSDG θ | After the canonical pair and checked vector bridges, `Region.Ordered.check` checks that every ordered root samples its own carried slot at the same pass. `Bundle.compile` emits numbered θ. `Bundle.returns_iff_observe` relates total-model finite returns to the fully defined ordered PEG tuple under the Boolean negation law. `Bundle.firstExit_of_returns` gives one common first pass and every defined prefix. `Peggy.Bridge.Theta.peggyToTheta` packages exact satisfaction on marked signatures and induced total models, using equality of finite-return relations. [Tuple checker](../../Silmaril/SSA/PEG/Bridge/Theta/Region/Tuple/Defs.lean) · [Tuple proofs](../../Silmaril/SSA/PEG/Bridge/Theta/Region/Tuple/Thms.lean) · [Comorphism](../../Silmaril/SSA/Peggy/Bridge/Theta/Thms.lean) · [#3344](https://github.com/hiloopai/silmaril-lean/pull/3344) · [#3993](https://github.com/hiloopai/silmaril-lean/pull/3993) · [#4012](https://github.com/hiloopai/silmaril-lean/pull/4012) · [#4047](https://github.com/hiloopai/silmaril-lean/pull/4047) |
| Checked PEG loop → native Isotope λSSA | `Region.LambdaSSA.lower` emits native guard, branch and backedge code. `lower_eval_iff` and `exists_runFuel_iff_observe` compare the typed packet and finite exit with Figure 11 under totality and negation. `Peggy.Bridge.Theta.LambdaSSA.peggyToNative` is a comorphism on the marked signature family. `thetaImage_agrees` checks its factorization through `peggyToThetaImage` and `thetaImageToNative`, which retain the scheduled image. The institutional observation compares finite exit-zero returns in induced pure total models with unit state. [Lowering theorems](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaSSA/Thms.lean) · [Comorphisms](../../Silmaril/SSA/Peggy/Bridge/Theta/LambdaSSA/Thms.lean) · [#4180](https://github.com/hiloopai/silmaril-lean/pull/4180) · [#4216](https://github.com/hiloopai/silmaril-lean/pull/4216) |
| Checked PEG loop → scalar MLIR SCF → CF | `Region.MLIR.lower` emits typed `scf.while`. `run_eq` compares each fuel budget with numbered θ. `returns_iff_observe` and `cf_returns_iff_observe` compare finite returns under the positive-width word profile and negation law. PEG inputs are decoded from typed MLIR words, with count operands decoded unsigned and Boolean operands in `i1`. Figure 11 pass indices remain natural numbers. [SCF/CF theorems](../../Silmaril/SSA/PEG/Bridge/Theta/Region/MLIR/Thms.lean) · [#4252](https://github.com/hiloopai/silmaril-lean/pull/4252) |
| Numbered RVSDG θ → scoped MLIR feedback | `RVSDG.MLIR.Graph.Feedback.WholeTheta.lower` handles a whole pure numbered θ graph with data-only carry. The PEG adapter `Region.MLIR.Scoped.lower` uses the numbered bundle. `returns_iff_numbered` compares the complete ordered finite return in the induced total model. `scf_returns_iff` relates the scoped block to the scalar SCF runner on the same width-indexed model and decoded values. The lowering emits scoped block syntax and the target theorem uses its relational `Block.Returns` semantics. [Numbered θ proof](../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Theta/Thms.lean) · [PEG adapter](../../Silmaril/SSA/PEG/Bridge/Theta/Region/MLIR/Scoped/Thms.lean) · [#4350](https://github.com/hiloopai/silmaril-lean/pull/4350) |
| Checked PEG loop → typed cyclic λRTL | `Region.LambdaRTL.lower` emits the mutable-register CFG, and `observeFuel` runs the target steps. `observeFuel_eq` relates target fuel `f` to `f / 2` numbered activations. `returns_iff_observe` compares the packed ordered tuple at the exit under totality and negation, projecting away the scratch store. [λRTL theorems](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaRTL/Thms.lean) · [#4295](https://github.com/hiloopai/silmaril-lean/pull/4295) |
| Exact 64-bit SCF image → machine RTL SSA | `Silmaril.Machine.PEG.CountedLoop.lower` requires an `Image` witness of the exact three-word `[count, left, right]` SCF template. `returns_iff_observe_bank` assumes correct nonzero, modular decrement/addition, and PEG negation. It characterizes finite `runMain` returns with the exact ordered bank and unchanged memory. The latch transfers `[count-1, right, left+right]` in parallel. This is a verified specialization over all admitted bank inputs and initial memories. Generic instruction selection, arbitrary schedules, physical register allocation and external ABI are outside its scope. The bridge goes through SCF, while the typed λRTL route is separate. [Template and lowering](../../Silmaril/Machine/PEG/CountedLoop/Defs.lean) · [Agreement](../../Silmaril/Machine/PEG/CountedLoop/Thms.lean) · [#4347](https://github.com/hiloopai/silmaril-lean/pull/4347) |

These loop bridges compare complete finite returns. General divergence,
trapping and effect correspondence require additional observations. General nested/effectful IR comorphisms would need their
own model and observation proofs. The structured target regressions check
two trips and zero trips; the machine fixture also checks modular wrap.
[Target regressions](../../tests/ssa/PEGStructuredTheta.lean)

## Java profile and experiments (§§8.1, 9 and Appendix A)

`Peggy.FieldHeap` implements resolved integer-field loads and stores and
proves guarded forwarding and disjoint-field laws. The observation
includes exact heap, sticky first fault and optional read values. A
completed faulting read is `some none`, distinct from PEG bottom `none`.
`FieldHeap.Linearize.run_eq_observe` proves exact ordered agreement for
an accepted straight-line single-token chain. The linearizer rejects
forks. The Java bytecode frontend, calls, arrays, allocation, full
exception semantics and general heap linearization remain open.
[Field proofs](../../Silmaril/SSA/Peggy/FieldHeap/Thms.lean) ·
[Linearizer](../../Silmaril/SSA/Peggy/FieldHeap/Linearize/Thms.lean) ·
[#3391](https://github.com/hiloopai/silmaril-lean/pull/3391) ·
[#3421](https://github.com/hiloopai/silmaril-lean/pull/3421)

The paper's timings, memory figures, 84% complete saturation, and 98%
validation of 3,416 Soot-optimized methods with three reported
miscompilations are historical measurements. Reproducing them requires
the Java engine, rule set, solver, Soot version, workloads and run
configuration. The Lean SIMPLE fixtures are executable proof regressions.
[§9](https://arxiv.org/pdf/1012.1802v3#page=65) ·
[§9.3](https://arxiv.org/pdf/1012.1802v3#page=69)

## Replay the end-to-end SIMPLE demo

Use a checkout of Silmaril with Git, Make, Python, Node.js and elan available. Fetch
the canonical PR ref, then create a detached worktree at the audited demo
commit. The checkout's `lean-toolchain` selects
`leanprover/lean4:nightly-2026-11-05` and its Lake manifest pins the dependencies.
[PR #3403](https://github.com/hiloopai/silmaril-lean/pull/3403) ·
[Demo contract and sources at the audited revision](https://github.com/hiloopai/silmaril-lean/blob/3fbdc9225cc9fa4ff6f507e1f4aee124127a2f9f/docs/projects/peggy-simple-validation.md)

```sh
git fetch origin refs/pull/3403/head
git worktree add --detach ../silmaril-peggy-demo 3fbdc9225cc9fa4ff6f507e1f4aee124127a2f9f
cd ../silmaril-peggy-demo
elan toolchain install "$(cat lean-toolchain)"
make check CHECK_TARGETS='+Silmaril.SSA.Peggy.SimpleValidation.Thms PEGCoreTests PeggyEggTests PeggySimpleValidationTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker Silmaril.Proofs.SSA.Peggy.SimpleValidation.Correctness
lake env leanchecker Silmaril.SSA.Peggy.SimpleValidation.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```

`Peggy.SimpleValidation.optimize` compiles typed loop-free single-result
SIMPLE, discovers and replays bounded contextual rewrites, selects a
candidate, and synthesizes and checks its reversion schedule.
`Peggy.SimpleValidation.Thms` exposes `Accepted.returns`,
`Accepted.runLoopFree` and `optimize_preserves_returns`. Given an accepted
result, rule laws and a successful source execution, the emitted SIMPLE
program returns the same value. Replay preserves exact ordered PEG
observations, including undefinedness. The entire pipeline has the narrower
successful-return contract and can reject a selected candidate during
reversion without searching for a fallback.

The standalone fixture uses `#guard_msgs` to check the results silently.
At input `(true, 14)`, depth zero leaves the reachable application count
at 5 and emits `add, add, add, bad`. Depth one lowers it to 4 and emits
`triple, add, bad`. Both return `some 84`. The false arm returns `none`
at depth one. A separate input program whose sharing would cause duplicate
writers is rejected with `Rejection.reversion`.
[Executable fixture](https://github.com/hiloopai/silmaril-lean/blob/3fbdc9225cc9fa4ff6f507e1f4aee124127a2f9f/tests/ssa/PeggySimpleValidation.lean)

## Replay the current cyclic and target fixtures

Use the audited main revision and its pinned Lean and Lake manifest.
`PeggyEggTests` checks the Figure 6 run, typed external-input discovery,
feedback legality, and scoped closure. `PEGCoreTests` and
`PEGCanonicalWhileTests` exercise structured admission and reversion.
`PEGStructuredThetaTests` runs the checked ordered loop through the
target evaluators above.

```sh
lake build --wfail PeggyEggTests PEGCoreTests PEGCanonicalWhileTests PEGStructuredThetaTests
lake env leanchecker tests.ssa.PeggyEgg
lake env leanchecker tests.ssa.PEGStructuredTheta
```

## Remaining work in priority order

1. **Compose cyclic selection with reversion across a larger structure.**
   `Structured.translate_figure19` already covers arbitrary structured
   frontend syntax. `Nested.Reindexed.Automatic.Accepted.returns_iff_observe`
   covers a recompiled two-level shape, and
   `Closed.Automatic.Recovered.exec_iff_firstExit` covers typed inputs
   for one loop under slice totality and the role laws. Build outward from
   those interfaces with checked placement, phase-correct boundaries
   and retained first-exit prefixes. General
   fusion and the paper's more advanced CFG reversion depend on this work.
2. **Connect executable saturation and profitability to their semantic
   specifications.** The abstract `NormalForms.paperNormalForm_unique`
   and the concrete `ZeroSampleAnalysis.monotone` proof are available.
   Coverage of a supplied finite `Dedup.close` scope leaves discovery
   and closure over new redexes to prove. Build the executable
   match/worklist refinement and independently checked cost-based
   selection. Extend guarded rule coverage with a definedness contract
   for each rule family needed by the remaining paper examples.
3. **Address completion and effects separately from Theorem 2.** A
   defined PEG return can leave an undefined or diverging source
   computation undemanded.
   Specify the additional completion or fault observation of Figure 18,
   then prove preservation through compilation and reversion for it.
   `FieldHeap.Linearize.run_eq_observe` is a starting point for one
   explicit effect chain, with general Java and §9 reproduction further
   downstream.

Three small implementation slices for the next round:

1. Add checked sequential composition of **two sibling loops** with a
   typed projected interface. Reuse single-loop `Region` or `Closed`
   schedules and prove first exits at the original coordinates for both
   loops. Include a zero-trip sibling and a repeated output. This extends
   extraction while staying within structured control flow.
2. Add a bounded worklist for `Extension.Dedup.close` that discovers
   eligible sites and checks newly generated rows. Distinguish exhausted
   fuel from a closed worklist. Prove that a closed result covers every
   eligible site in the resulting table and preserves observations under
   the zero law.
3. Add bounded representative enumeration with an explicit additive
   cost and a minimum theorem over the enumerated **legal** candidates.
   Require checked row equality, `FeedbackRank`, and the applicable
   Figure 19/demand/schedule witnesses for each candidate. Use a small
   cyclic graph where the cheapest unchecked representative is illegal.
   This gives a reference for checking a later pseudo-Boolean encoding.
