# Peggy paper coverage and reproduction

Silmaril proves the repaired Figure 11 denotation and structured SIMPLE
forward preservation. It also proves successful completion for the
Figure 18 compiler fragments through one conditional child. Checked
worklist replay can feed ordered SIMPLE selection, and checked reversion
covers single loops, a parent/child form and a pair of sibling loops.
General reversion, the full Peggy engine and the historical Java
experiments remain open.

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
[Audited main commit](https://github.com/hiloopai/silmaril-lean/tree/c135a1e05290a98c24a966d79bc8ba00fc35187b)

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
fixture checks the latter. Figure 18 adds a separate observation, covered
by the compiler fragments below. The authors' Coq `PEGSem.v` samples
eval's selected index directly. Figure 11 and Lean require a defined
prefix up to that index.
[Thm. 2 and Fig. 18](https://arxiv.org/pdf/1012.1802v3#page=36) ·
[Coq source](https://cseweb.ucsd.edu/groups/progsys/peg-coq-proof/PEGSem.v) ·
[Source semantics and comparison](peg-simple.md#comparison-with-the-authors-coq)

### Figure 18 completion

The completion compiler adds a second ordered root to a returned data
value. Its fresh Boolean seed is true. Each strict assignment links its
value and the previous marker with an `after` operation, even when a
later projection discards that value. A branch joins the marker and live
slots with the same lazy φ guard. Each while samples its carried marker
at the ordinary Figure 11 first pass. This uses the existing pass and
eval operators to encode completion. The paper sketches an extra token
argument and result on pass itself.
[§6.4 and Fig. 18](https://arxiv.org/pdf/1012.1802v3#page=39) ·
[Token compiler](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Defs.lean#L124)

For the compiled fragments below, a successful original SIMPLE return
defines `[some value, some true]`. A **defined marker alone** guarantees a
finite successful execution of the original source with the corresponding
data result. `translate_demandWellFounded` supplies the native Figure 11
denotation, and the proofs assume the Boolean negation law. They allow
partial source primitives. Source failure and divergence both leave the
marker bottom. Data can still be defined. Java exceptions, failure
causes and observable traces require richer observations.

| Landed fragment | API and fixture |
| --- | --- |
| Precursor for the ordinary translation | `Structured.translate_while_returns_of_checkedPrefix` constructs a successful original return from a defined ordinary pass and data root plus `checkWhilePrefix` for the guard and full loop-free body along the finite prefix. The prefix check is a premise of this theorem. [Theorem](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Thms.lean#L41) · [Discarded failure fixture](../../tests/ssa/PEGSimple.lean#L631) · [#4615](https://github.com/hiloopai/silmaril-lean/pull/4615) |
| One while with a loop-free body, including branches | `Token.translate` compiles assignments, projections, sequences and conditionals via `Body.ofStmt`. `Token.observe_of_returns` and `Token.returns_of_completion` prove both directions. The fixture exercises selected and unselected failing assignments and zero trips. [Forward theorem](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Thms.lean#L41) · [Converse](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Thms.lean#L51) · [Conditional fixture](../../tests/ssa/PEGSimple.lean#L904) · [#4650](https://github.com/hiloopai/silmaril-lean/pull/4650) · [#4683](https://github.com/hiloopai/silmaril-lean/pull/4683) |
| One unconditional child per continuing parent step | `Token.Nested.Form.translate` uses projection-only captures, a loop-free child body and a loop-free outer commit. The child marker starts from the current outer marker. `Form.trace_of_completion` returns an actual outer `WhileTrace`, its exact pass count and a finite child pass and completion witness at every continuing outer coordinate. `Form.returns_of_completion` reconstructs the original return. The countdown uses child lengths two and one and returns `4`. [Compiler](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Defs.lean#L64) · [Return theorem](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Thms.lean#L54) · [Trace theorem](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Thms.lean#L45) · [Fixture](../../tests/ssa/PEGSimple.lean#L493) · [#4718](https://github.com/hiloopai/silmaril-lean/pull/4718) |
| One child in a selected outer arm | `Token.Nested.Conditional.Form.translate` adds a decision on the old outer store. The take arm runs the captured child and commit. The skip arm runs a loop-free update. `Form.trace_of_completion` gives the outer trace and a defined decision at each continuing coordinate, with child pass and marker evidence only for a true decision. `Form.observe_of_returns` and `Form.returns_of_completion` give the return equivalence for this form. The fixture takes, skips, then takes with child lengths three and one and returns `7`. A second fixture shows a discarded partial child computation blocks completion when taken and is undemanded when skipped. [Compiler](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Conditional/Defs.lean#L69) · [Activation predicate](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Conditional/Defs.lean#L87) · [Forward theorem](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Conditional/Thms.lean#L35) · [Trace theorem](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Conditional/Thms.lean#L45) · [Converse](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Conditional/Thms.lean#L54) · [Mixed-trace fixture](../../tests/ssa/PEGSimple.lean#L537) · [Partial-child fixture](../../tests/ssa/PEGSimple.lean#L1211) · [#4762](https://github.com/hiloopai/silmaril-lean/pull/4762) |

These equivalences are proved for their respective compiler inputs.
A recursive completion compiler and proof for arbitrary typed structured
SIMPLE, preservation through general reversion, and a richer effect or
fault observation remain open.
[Compiler walkthrough](peggy-figure18-token.md) ·
[Conditional child walkthrough](peggy-figure18-conditional-child.md)

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

`Nested.Region.check` checks a supplied descriptor and demand rank on
the original table. It checks each shared pass, the ordered parent and
child θ bundles, child eval roots and the designated parent eval.
Primitive schedules initialize the child from the current outer store
and commit simultaneously from child exits and old outer captures.
`Accepted.activation_observation` fixes the outer coordinates and starts
the child at its own zero index. `Accepted.observe_of_returns` recovers
the Figure 11 observation from a successful emitted SIMPLE run under the
negation law. [Checker](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Defs.lean#L92) ·
[Activation theorem](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Thms.lean#L25) ·
[#4412](https://github.com/hiloopai/silmaril-lean/pull/4412)

`Accepted.trace_of_exits` and `Accepted.returns_iff_exits` give the
converse under `Accepted.DefinedSlices` and the negation law. The PEG
premises are a finite parent first pass, a finite child first pass at
**each continuing outer coordinate**, and a defined designated value
for the return theorem. The child counts can vary by activation. The
child premise is vacuous for zero outer trips. The slice premise covers
the full guard, capture initialization, child update and outer commit
where used. Total primitives discharge the slice premise. Finite child exits remain
separate hypotheses. This is a different converse from the
Figure 18 compiler's defined-marker theorem.
[Trace](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Thms.lean#L78) ·
[Return equivalence](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Thms.lean#L101) ·
[#4489](https://github.com/hiloopai/silmaril-lean/pull/4489)

`Nested.Region.Automatic.extract` recovers a descriptor from the graph,
a supplied demand rank and the negation opcode, then runs the same
checker on the original numbered table. It needs a singleton outer eval
root, a unique child and child pass, one outer θ per input initializer,
and exactly one child eval projection per child θ at the shared pass.
`Recovered.returns_iff_exits` exposes the same conditional finite-return
contract. The fixture recovers the two-level region after row and loop
renumbering, rejects a stale capture and a mismatched pass, and derives
the emitted trace for zero and two parent trips (child counts two and
one). General discovery or extraction for arbitrary loop forests and
effects remains open.
[Extractor](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Automatic/Defs.lean#L91) ·
[Recovered contract](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Automatic/Thms.lean#L33) ·
[Regression](../../tests/ssa/PEGCanonicalWhile.lean#L969) ·
[Trace from PEG equations](../../tests/ssa/PEGCanonicalWhile.lean#L1192) ·
[#4520](https://github.com/hiloopai/silmaril-lean/pull/4520)

### Sequential sibling loops

`While.Siblings.check` accepts a supplied pair of checked parentless
primitive loop certificates with a typed projection between them. It
checks their row correspondence, port order and demand rank against the
original two-key graph. `Accepted.exec_iff_observations` compares a
successful emitted sequence with both first passes and both ordered
observations. The converse uses each stage's whole-slice totality and the
zero, tick and negation laws. The fixture checks the intermediate
`[3, 10, 2, 3]`, final `[13, 3, 3, 13]` and rejection of mismatched
same-sort handoff ports. This interface takes two stages and their
wiring as input.
[Checker](../../Silmaril/SSA/PEG/Simple/Revert/While/Siblings/Defs.lean#L104) ·
[Correspondence](../../Silmaril/SSA/PEG/Simple/Revert/While/Siblings/Thms.lean#L51) ·
[Regression](../../tests/ssa/PeggyEgg.lean#L2047) ·
[#4460](https://github.com/hiloopai/silmaril-lean/pull/4460)

## Saturation, selection and worked optimization

### Section 4 and the saturation engine

| Paper claim | Proved or implemented boundary |
| --- | --- |
| (4.1) and (4.2) | `NormalForms.Inflationary` says each analysis step extends its source. `MonotoneSimulation` says that after enlarging the source, the **same analysis** has a step whose result covers the smaller step's result. A simulated step may stutter. For concrete E-PEG append receipts, `Step.embedding` proves (4.1). The comparison uses typed injections preserving rows, ordered roots, forest and old class equalities. `ZeroSampleAnalysis.inflationary` and `ZeroSampleAnalysis.monotone` verify both assumptions for fresh zero-sample generation. [Abstract definitions](../../Silmaril/SSA/Peggy/EPEG/Saturation/NormalForms/Defs.lean) · [Concrete proofs](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Comparison/Thms.lean) · [#4072](https://github.com/hiloopai/silmaril-lean/pull/4072) · [#4096](https://github.com/hiloopai/silmaril-lean/pull/4096) |
| (4.3) and (4.4) | `NormalForms.delayed_step` needs simulation of the delayed analysis and inflationarity of the intervening analysis. `stableNormalForm_least` and `stableNormalForm_unique` assume a reflexive, transitive comparison and inflationarity plus simulation for **every** family member. Every step out of a stable state is covered by that state. Two reachable stable states mutually compare. `paperNormalForm_unique` additionally assumes antisymmetry and proves literal equality for the paper's identity-filtered terminal forms. The E-PEG embedding corollary gives mutual embeddings. These are conditional uniqueness results. `ZeroSample.no_stable` shows that fresh appending from a matched site leaves strict progress in every reachable state. [Abstract proofs](../../Silmaril/SSA/Peggy/EPEG/Saturation/NormalForms/Thms.lean) · [E-PEG specialization](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Comparison/Thms.lean) · [§4](https://arxiv.org/pdf/1012.1802v3#page=19) · [#4111](https://github.com/hiloopai/silmaril-lean/pull/4111) |
| Executable closure (§8.2) | `Saturation.saturate` closes a supplied finite table of ground obligations. `saturate_least`, `saturate_perm` and `run_denote_sound` cover that fixed table, with semantic validity of rule obligations. `Extension.Plan.run` replays a supplied prefix that appends typed rows, with soundness under the corresponding receipt laws. `Extension.Dedup.close` reuses or appends the exact zero-sample RHS for a caller-supplied site list. `close_checked` requires initial eligibility, `close_fixed` proves re-running a checked closed scope stutters, and `close_sound` uses the zero law. [Fixed table](../../Silmaril/SSA/Peggy/EPEG/Saturation/Thms.lean) · [Append replay](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Thms.lean) · [Scoped closure](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Dedup/Thms.lean) · [#3313](https://github.com/hiloopai/silmaril-lean/pull/3313) · [#4138](https://github.com/hiloopai/silmaril-lean/pull/4138) |
| Zero-sample worklist (§8.2) | `Dedup.Worklist.run` scans the current table for enabled zero-sample visits, including newly appended redexes. `check_normalForm` proves reachable stability for a checked `.fixed` receipt in the `Visits` family. `check_exhausted` certifies budget use with an enabled site remaining. Termination to closure, uniqueness for this visit policy and reusable worklist/Rete refinement for a broader rule family remain open. [Worklist entry](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Dedup/Worklist/Defs.lean#L58) · [Closure theorem](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Dedup/Worklist/Thms.lean#L86) · [Worklist fixture](../../tests/ssa/PeggyEgg.lean#L1180) · [#4408](https://github.com/hiloopai/silmaril-lean/pull/4408) |

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

### From a worklist receipt to ordered SIMPLE

`Cost.selectWith` checks candidates from a supplied finite list. Its
legality checks combine row/class and root alignment, native demand
rank, and the actual feedback-edge rank. The emitter is another admission
gate. `selectWith_min` ranges only over entries admitted by these gates
at the supplied cost. `Cost.Bundle.select` adds an ordered emitter for a
primitive, parentless single loop with direct carried-slot eval roots
sharing one pass. It preserves order, duplicates and partial PEG values.
[Selector](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Defs.lean#L85) ·
[Minimum theorem](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Thms.lean#L66) ·
[Ordered emitter](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Defs.lean#L25) · [Bundle selector](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Defs.lean#L34) ·
[#4463](https://github.com/hiloopai/silmaril-lean/pull/4463) ·
[#4505](https://github.com/hiloopai/silmaril-lean/pull/4505)

`Cost.Bundle.Worklist.check` reconstructs the exact endpoint graph and
partition from the original state and the zero-sample address receipt.
`CheckedReceipt.select` takes a pool typed at that endpoint and its
`select_min` compares all admitted pool entries. Both a checked
`.fixed` receipt and a checked `.exhausted` receipt can feed selection.
Closure of the current table for this rule and minimum cost in the
supplied pool are independent claims. Selection keeps the first admitted
minimum in pool order and returns `none` if no entry passes.

`CheckedReceipt.observe_eq` preserves the original ordered Figure 11
tuple, including bottom, under the defined-zero law, source demand
well-foundedness and initial class validity. `observe_of_exec` transports
a successful emitted SIMPLE execution to that original observation under
the negation law. `exec_iff_observe` gives the finite-execution converse
for a fully defined tuple with total guard and complete update. The
regression checks `[2, 17, 2]` after either stop status and rejects the
same redirected index with singleton classes. General candidate
enumeration and the paper's global profitability and reversion
guarantees remain open.
[Receipt check](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Defs.lean#L30) ·
[Receipt selector](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Defs.lean#L42) ·
[Pool minimum](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Thms.lean#L36) ·
[Observation equality](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Thms.lean#L53) ·
[Execution equivalence](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Worklist/Thms.lean#L78) ·
[Regression](../../tests/ssa/PeggySimpleValidation.lean#L547) ·
[#4537](https://github.com/hiloopai/silmaril-lean/pull/4537)

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

### Signatures that change data sorts

`Peggy.SortMap.inst` uses signatures carrying their own data sorts.
An arrow maps data sorts (possibly identifying them) and opcodes at the
mapped ordered profiles. Boolean and count sorts stay fixed. On the
reusable PEG side, `Graph.mapData` transports ordered ports by position.
`Graph.observe_denote_mapData` transports every optional root at every
index. The reduct pulls target carriers back along the sort function.
`Peggy.SortMap.Equation.holds_map` is exact satisfaction of mapped open
equations in the target model versus the reduct.
`Peggy.SortMap.fixedComparison` is the bundled comorphism from a
fixed-sort Peggy institution to this one, using the same local sentences
and models on identity-sort arrows. The regression identifies two
distinct source sorts and retains two ordered inputs `2` and `9` and
ordered results `11` and `9` at iteration one. The theorem is about
transport by profiles and pullback carriers. It supplies no arbitrary
carrier conversion or new IR endpoint.
[Graph transport](../../Silmaril/SSA/PEG/SortMap/Defs.lean#L87) ·
[Observation theorem](../../Silmaril/SSA/PEG/SortMap/Thms.lean#L80) ·
[Satisfaction](../../Silmaril/SSA/Peggy/Institution/SortMap/Thms.lean#L46) ·
[Institution](../../Silmaril/SSA/Peggy/Institution/SortMap/Thms.lean#L65) ·
[Comorphism](../../Silmaril/SSA/Peggy/Institution/SortMap/Thms.lean#L89) ·
[Regression](../../tests/ssa/PeggySortMap.lean#L112) ·
[#4574](https://github.com/hiloopai/silmaril-lean/pull/4574)

### IR bridges

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

The regionless, marked θ and marked native λSSA arrows named above are
bundled comorphisms with satisfaction and model comparison. The SCF/CF,
scoped feedback MLIR, λRTL and exact machine RTL entries give semantic
lowering theorems for the stated profiles. The bundled IR arrows use
their own fixed-sort signatures. The loop bridges compare finite complete
returns. General nesting needs additional lowering proofs, and
divergence, traps and effects need richer observations. The structured
target regressions check two trips and zero trips. The machine fixture
also checks modular wrap.
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
`PEGCanonicalWhileTests` exercise structured admission, Figure 18
completion and checked parent/child reversion.
`PeggySimpleValidationTests` checks receipt-to-selection and emitted
execution, and `PeggySortMapTests` checks non-injective sort transport.
`PEGStructuredThetaTests` runs the checked ordered loop through the
target evaluators above.

```sh
lake build --wfail PeggyEggTests PEGCoreTests PEGCanonicalWhileTests PeggySimpleValidationTests PeggySortMapTests PEGStructuredThetaTests
lake env leanchecker tests.ssa.PeggyEgg
lake env leanchecker tests.ssa.PEGStructuredTheta
```

## Remaining work in priority order

1. **Make completion recursive over typed SIMPLE.** Lift the tokenized
   store invariant from `Token.Body.lower` to `Stmt P true` by reusing
   the existing structured builders. Prove one scope-indexed
   correspondence for a statement with an incoming token, first for
   composition and then for a `while` whose body uses that same theorem
   recursively. Test it by deriving both existing child forms from the
   common compiler. This targets a single successful-completion
   equivalence for arbitrary typed programs. Distinguishing finite
   failure from divergence needs a richer observation and belongs in a
   separate theorem.
2. **Give reversion a typed, recursive schedule.** Refactor the checked
   sibling handoff and the parent/child activation into schedule
   constructors with ordered input and output ports and explicit
   observations at the enclosing coordinates. Prove composition for a
   sequence of any length from `Siblings.Accepted.exec_iff_observations`
   and reuse `Nested.Region.Accepted.trace_of_exits` for a loop region.
   Put existing examples through the same checker before extending
   branch placement and automating descriptor discovery. This is a
   step toward reversion from inward Figure 19 evidence. General
   schedule existence, loop and branch fusion, and the paper's
   placement completeness still need proofs.
3. **Generalize replay before broadening profitability.** Parameterize
   the checked `Dedup.Worklist` driver by a rule's match, extension,
   class update, coverage and preservation interfaces. Instantiate it
   with zero sampling and one independently proved guarded rule.
   Relate checked closure to stability for their combined visit family.
   The conditions of (4.1)–(4.4) must be proved for that family before
   using its uniqueness theorem. Then connect a finite enumeration of
   legal candidates to `Cost.selectWith_min`, with coverage of that
   enumeration stated explicitly. The paper's Rete engine, general
   weighted pseudo-Boolean selection, and the remaining Appendix A
   rules stay separate obligations.

The Java frontend, general effect/token semantics and the historical
evaluation remain downstream. Those results require source and target
observations for effects, plus separate benchmark reproduction.
