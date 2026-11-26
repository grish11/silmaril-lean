# Peggy paper coverage and reproduction

Silmaril has a typed PEG core, a repaired Figure 11 denotation, a structured
SIMPLE forward preservation proof, and several checked optimization and
reversion paths. The end-to-end replay below exercises the loop-free path.
The literal statement of Theorem 1 has a counterexample, and the general
reverter and historical Java experiments remain open.

The reference is Ross Tate, Michael Stepp, Zachary Tatlock and Sorin Lerner,
*Equality Saturation: A New Approach to Optimization*, LMCS 7(1:10), 2011,
arXiv:1012.1802v3, 80 PDF pages. SHA-256 of the PDF is
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.
Page links use PDF page numbers. PEG denotes **Program Expression Graph**.
[Paper](https://arxiv.org/pdf/1012.1802v3) · [Journal](https://lmcs.episciences.org/1016)

**Proved** refers to the stated Lean theorem under its listed hypotheses.
**Implemented** refers to executable code or fixtures with their stated
acceptance boundary. **Open** marks a missing or unsupported paper claim.
PR numbers identify canonical review artifacts, including work that may be
ahead of main. Module names below omit the common `Silmaril.SSA.` prefix.

## Graphs, forward translation and examples

| Paper locator | Coverage in Lean | Open or different |
| --- | --- | --- |
| §§1–3, worked optimizations | **Implemented and checked examples.** `tests/ssa/PEG.lean` exercises typed sharing, lazy branching and loop feedback. `tests/ssa/PEGSimple.lean` checks factorial and later sibling, branch-contained and nested loops. Selected rules and bounded optimization have independent fixtures. [Paper](https://arxiv.org/pdf/1012.1802v3#page=2) · [#3205](https://github.com/hiloopai/silmaril-lean/pull/3205) · [#3335](https://github.com/hiloopai/silmaril-lean/pull/3335) · [#3375](https://github.com/hiloopai/silmaril-lean/pull/3375) | The paper's full sequence of example optimizations, including inter-loop strength reduction and branch hoisting, has no complete replay. |
| §5.1, Fig. 11, Def. 5.1 and Thm. 1 | **Implemented** typed, numbered graphs in `PEG.Defs` and wiring checks in `RawGraph.check` in `PEG.Builder`. **Proved** structural and demand lemmas in `PEG.Thms` and `PEG.Semantics.Thms`, including `Graph.existsUnique_solves_of_wellFormed`, `Graph.demandWellFounded_of_check` and `Graph.observe_denote_mapOps`. [#3205](https://github.com/hiloopai/silmaril-lean/pull/3205) · [#3253](https://github.com/hiloopai/silmaril-lean/pull/3253) | Lean's structural guard strengthens the printed guard. See the discrepancy below. |
| §5.3, Def. 5.2 and Appendix A | **Proved** the largest syntactic invariance predicate and its semantic consequence in `PEG.Rules.Thms` (`invariantAt_largest`, `denote_invariant`), plus guarded rules including `phi_same_of_defined`, `theta_self`, `eval_invariant` and `pass_peel`. [#3358](https://github.com/hiloopai/silmaril-lean/pull/3358) | Open: the remaining discharge conditions and rules for the paper's partial-stream and language-specific examples. For example, `φ(c,a,a) = a` needs a defined condition for the Lean rule. Appendix A itself lists only rules relevant to Fig. 38, a subset of the historical engine's rules. |
| §6, Figs. 15 and 17, Thm. 2 | **Implemented** typed positional variables, primitive applications, fresh assignments, context projection, sequence, branches, while and one return. **Proved** `Program.translate_returns` in `PEG.Simple.Thms` (loop-free), `WhileProgram.translate_returns` in `PEG.Simple.While.Thms` (top-level while), and `translate_returns` in `PEG.Simple.Structured.Thms` (compositional loops). The structured compiler derives first exits and defined eval prefixes from finite source execution at fixed enclosing coordinates. It requires the supplied Boolean negation opcode to implement negation. `Structured.translate_wellFormed` proves the emitted graph itself meets Peggy's structural sentence admission. [#3306](https://github.com/hiloopai/silmaril-lean/pull/3306) · [#3335](https://github.com/hiloopai/silmaril-lean/pull/3335) · [#3375](https://github.com/hiloopai/silmaril-lean/pull/3375) · [#3427](https://github.com/hiloopai/silmaril-lean/pull/3427) | Successful source return implies the same defined PEG result (the structured theorem holds at every output index, including the paper's all-zero index). Failure and divergence are outside that implication. |

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

## Saturation, reversion and implementation

| Paper locator | Coverage in Lean | Open or different |
| --- | --- | --- |
| §4, Fig. 10 and (4.1)–(4.4); §5.2; §8.2 | **Implemented** sorted Egg explanation replay for ranked acyclic graphs and a guarded cyclic E-PEG certificate kernel. **Proved** `checkOutputs_figure11_sound` in `Peggy.Bridge.Figure11.Thms`, `observe_sound_of_rows` in `Peggy.EPEG.Selection.Thms`, and `saturate_least`, `saturate_perm`, `run_denote_sound` in `Peggy.EPEG.Saturation.Thms`. Saturation closes the partition on a fixed finite node table and supplied ground obligations. Semantic rule hypotheses or checked structural evidence justify the corresponding equalities. [#3256](https://github.com/hiloopai/silmaril-lean/pull/3256) · [#3284](https://github.com/hiloopai/silmaril-lean/pull/3284) · [#3313](https://github.com/hiloopai/silmaril-lean/pull/3313) | Open: (4.1)–(4.4) for general node-generating monotone analyses, and the correspondence of a Rete engine and its bounded worklist with that semantics. |
| §8.3, search and `SelectBest` | **Implemented** bounded single-root discovery and contextual ranked loop-free search. **Proved** `Candidate.sound` in `Peggy.Optimizer.Thms`, `optimize_min` and `compareOutputs_sound` in `Peggy.Optimizer.Contextual.Thms`. The contextual measure is the count of distinct reachable primitive and φ vertices, minimized among the explored, replay-checked candidates. `Result.sound` in `Peggy.Optimizer.Cyclic.Thms` covers elimination of a literal θ self-feedback row with a leaf initializer under a single-loop admission check excluding eval/pass. [#3346](https://github.com/hiloopai/silmaril-lean/pull/3346) · [#3372](https://github.com/hiloopai/silmaril-lean/pull/3372) · [#3413](https://github.com/hiloopai/silmaril-lean/pull/3413) | Open: general cyclic discovery and extraction across eval/pass boundaries, and the paper's pseudo-Boolean costs, constraints, solver integration and optimality claim. |
| §7.1–7.5, Fig. 19 | **Proved** `Certificate.revert_returns` and `Certificate.revert_run` in `PEG.Simple.Revert.Thms` for a checked, supplied single-output loop-free schedule. **Implemented** partial automatic ranking/scheduling in `PEG.Simple.Revert.Automatic`; `checkRanked_accepts_straightLine` proves acceptance for a narrower straight-line class. **Implemented** exact-recompilation extraction of a canonical seven-row scalar loop in `PEG.Simple.Revert.While`, with `Certificate.compile_eq` and source-return-to-observation `Certificate.observe_of_returns`. The ten-row pair extractor in `PEG.Simple.Revert.While.Pair` uses simultaneous updates from the old store. Its `Certificate.returns_of_defined` and the scalar counterpart recover source returns from defined PEG observations under guard and complete-step totality and the negation law. The pair fuel runner also has `Certificate.runFuel_of_defined`. **Implemented and proved** `PEG.Simple.Revert.While.Region.Automatic.extract` infers a typed boundary, demand rank and schedules for a restricted parentless single loop without compiler row numbering. `Certificate.returns_iff_observe` relates the emitted SIMPLE return to the original Figure 11 observation under guard and full-update totality and the negation law. `Certificate.exitWitness_of_defined` gives the finite first pass and the eval prefix. **Implemented and proved** `PEG.Simple.Revert.While.Nested.Automatic` infers a two-level form from the designated eval, parent table and scoped wires and validates it against the existing structured compiler table. Its `Accepted.returns_iff_observe` covers one scoped inner invocation per outer step. [#3760](https://github.com/hiloopai/silmaril-lean/pull/3760) · [#3725](https://github.com/hiloopai/silmaril-lean/pull/3725) · [#3703](https://github.com/hiloopai/silmaril-lean/pull/3703) · [#3348](https://github.com/hiloopai/silmaril-lean/pull/3348) · [#3388](https://github.com/hiloopai/silmaril-lean/pull/3388) · [#3389](https://github.com/hiloopai/silmaril-lean/pull/3389) · [#3441](https://github.com/hiloopai/silmaril-lean/pull/3441) | Open: general Figure 19 recognition, a proof that structured compilation produces that class, and general loop/branch extraction and sequencing. Structural `WellFormed` alone does not supply a reversion schedule. The graph-only single-loop checker requires one θ per initializer port and the eval/pass phase layout. |
| §7.6–7.9, optimized reversion | **Implemented** restricted sharing-aware placement with rejection in the loop-free scheduler, and simultaneous old-store updates with shared primitive bindings in the checked single-loop region. [#3388](https://github.com/hiloopai/silmaril-lean/pull/3388) · [#3441](https://github.com/hiloopai/silmaril-lean/pull/3441) | Open: simultaneous-copy scheduling across general control flow, loop and branch fusion, redundancy hoisting, MustEval and LICM. |
| §8.1 and Appendix A, Java | **Implemented and proved** resolved integer-field loads/stores in `Peggy.FieldHeap.Thms`, including guarded forwarding and disjoint-field laws. Observations include exact heap, sticky first fault and optional read values; a completed faulting read (`some none`) differs from PEG bottom (`none`). `run_eq_observe` in `Peggy.FieldHeap.Linearize.Thms` proves exact ordered observation for an accepted straight-line single-token chain. [#3391](https://github.com/hiloopai/silmaril-lean/pull/3391) · [#3421](https://github.com/hiloopai/silmaril-lean/pull/3421) | Open: Java bytecode conversion, full object/array/allocation/call and exception semantics, and general heap linearization. The linearizer rejects token forks. |
| §8.4, separate eval and pass | **Implemented and proved** the split in `PEG.Semantics.Thms`. The structured frontend shares one pass across the evals of the carried values for each loop. [Paper](https://arxiv.org/pdf/1012.1802v3#page=65) · [#3253](https://github.com/hiloopai/silmaril-lean/pull/3253) · [#3375](https://github.com/hiloopai/silmaril-lean/pull/3375) | The split is part of the denotation. General optimization and reversion across these nodes remain open. |
| §9 and Fig. 38, empirical evaluation | **Reproducible fixture** for one typed SIMPLE pipeline below. | **Historical measurements:** the timings and space results, 84% complete saturation, and validation of 98% of 3,416 Soot-optimized methods with three reported miscompilations require the original Java toolchain, rules, workloads and experiment configuration. No Lean reproduction of those measurements is delivered here. [§9](https://arxiv.org/pdf/1012.1802v3#page=65) · [§9.3](https://arxiv.org/pdf/1012.1802v3#page=69) |

The graph-only checker starts at the designated eval and reads the sampled
θ, the shared pass and its unary Boolean exit operation. It orders carried
values by the typed parameter ports that initialize them. Each port must
initialize exactly one θ and the table must contain exactly that many θs.
Duplicate or missing θ initializers are rejected, even on unused rows.
The existing supplied-boundary checker remains available.

The inferred rank separates eval, pass and interior rows by label,
compares the iteration counter next, then synthesizes heights on the
remaining same-phase, same-index edges by removing sinks. The existing
demand checker validates all graph rows. Each φ-free slice starts with the
old θ vector, emits each primitive row once, and rejects reads of a pass,
eval or undeclared θ. `Automatic.extract_accepts` proves recognition
relative to a schedulable region boundary with unique θ initializers and
a bounded rank in this phase layout.
The update slice commits the entire typed vector at once. SIMPLE caches
the guard in a loop-local slot to keep multi-row guards executable with
the existing while syntax. The correspondence concerns defined returns.
A partial update whose result the PEG never demands can prevent a SIMPLE
return, so the reverse direction requires totality of the complete update.
[`Automatic.Defs`](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Automatic/Defs.lean) ·
[`Automatic.Thms`](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Automatic/Thms.lean) ·
[Regression fixture](../../tests/ssa/PEGCanonicalWhile.lean)

The two-level reversion form uses a typed capture projection on the old
outer vector, one child while with a loop-free body, and a loop-free commit
from the child's full final store to the next outer vector. The child and
commit can access only their local contexts. An old value needed at commit
is carried through an explicit capture slot. The checker compares the
numbered table and loop parents with the existing structured lowering of
this form, including the capture, feedback, and exit wires.

The automatic entry point follows the designated eval to the outer pass
and selects the unique direct child pass. The shared eval bundle of
each loop identifies its ordered θ slots. Child initializers must read
the outer θ vector and may repeat a capture. The child update reads only
the child θ vector and local primitive assignments. The commit reads
only the child eval bundle and its own primitive assignments. Each guard
is a carried Boolean or a single primitive over its carried values. Both
loops use the same unary Boolean negation opcode. The probe follows
dependency edges and reuses the checked primitive scheduler. It orders
bundles and assignments by the structured compiler's row order, then
passes the inferred form to the exact-table checker. Primitive assignments
must be reachable from feedback or commit roots in their respective
slices. The graph-only API supports the numbered compiler layout with the
loop-ID space indexed by rows. General numbered layouts remain open.

`Structured.translate_while_trace_of_defined` recovers a finite outer trace
from a defined eval using the first pass and the selected sample prefix.
Every continuing outer store must have a successful complete body step.
For the checked two-level form, this requires the guard to be total, the
child to terminate successfully on continuing captures, and the commit
to succeed on completed child stores. The Boolean negation law relates
the exit flag to the continuation test. Successful SIMPLE returns imply defined PEG observations by the existing
structured compiler theorem. The executable fixture recovers two valid
capture layouts and rejects a child initializer that reads outside the
outer θ vector and a missing child parent.
[`Nested.Automatic.Defs`](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Automatic/Defs.lean) ·
[`Nested.Automatic.Thms`](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Automatic/Thms.lean) ·
[Regression fixture](../../tests/ssa/PEGCanonicalWhile.lean)

Two printed details need explicit treatment in a full formalization.
Figure 19's Type-Eval-Pass premise is `ℓ = ℓ′ + 1`, with `ℓ` the
surrounding depth and `ℓ′` the sampled loop's depth. Sampling an immediate
child from its parent calls for `ℓ′ = ℓ + 1`. Section 8.3's displayed
cycle constraints exclude cycles without a θ node. A θ whose initializer
selects itself still passes that test, although Definition 5.1(1) requires
a feedback edge on the cycle. A general CFG-like checker and a legality
proof for selection must account for both details.
[Fig. 19](https://arxiv.org/pdf/1012.1802v3#page=41) ·
[§8.3 constraints](https://arxiv.org/pdf/1012.1802v3#page=64)

## Dialects, institutions and IR bridges

These are Silmaril extensions to the paper. The direction of each arrow
below is the sentence or program translation direction. Comorphism
models are pulled back in the opposite direction.

| Interface | Proved scope |
| --- | --- |
| `Peggy.Dialect.sentenceFunctor`, `Peggy.Institution.inst`, `Peggy.Dialect.Equation.holds_map` | The signature category fixes the sorts and maps opcodes forward, preserving ordered operand/result profiles. The sentence functor relabels equations of structurally admitted PEGs. The contravariant model functor takes reducts of discrete partial interpretations. Satisfaction is equality of ordered optional values for every defined input tuple and every index. `Peggy.Institution.Family.Defs` supplies `familyComorphism` and `familyChange` for functorial dialect families. [#3229](https://github.com/hiloopai/silmaril-lean/pull/3229) · [#3380](https://github.com/hiloopai/silmaril-lean/pull/3380) |
| Many-sorted equational logic → total-primitive Peggy | `Peggy.Bridge.Equational.Thms`: `comorphism`, `exact_satisfaction`, `modelExpansive`, `entails_compile_iff`. Term compilation and model expansion give entailment equivalence for the stated total-primitive subinstitution. [#3414](https://github.com/hiloopai/silmaril-lean/pull/3414) |
| Ordered value PEG → regionless RVSDG → regionless MLIR | `observe_translate` in `PEG.Bridge.RVSDG.Thms` and `observe_translateMLIR` in `PEG.Bridge.MLIR.Thms` cover ordered zero-loop pure PEGs with total primitives and the induced models. `Peggy.Bridge.IR.Thms` bundles `peggyToRVSDG`, `rvsdgToMLIR`, `peggyToMLIR` and `peggyToMLIR_modelExpansive` for the restricted institutions. [#3291](https://github.com/hiloopai/silmaril-lean/pull/3291) · [#3376](https://github.com/hiloopai/silmaril-lean/pull/3376) |
| Canonical PEG loop → structured RVSDG θ | `returns_iff_observe` in `PEG.Bridge.Theta.Thms` relates the RVSDG return to the PEG first-exit observation for the canonical total two-carried-slot, single-loop form. [#3344](https://github.com/hiloopai/silmaril-lean/pull/3344) |
| Ordered value PEG → RVSDG → typed λRTL/forward CFG; scoped PEG diamond → λSSA | `observeCFG_peg` in `PEG.Bridge.ForwardCFG.Thms` covers the ordered zero-loop total value path. `ScopedDiamond.lower_eval_iff` in `PEG.Bridge.LambdaSSA.Thms` covers the scoped zero-loop diamond. General looping/effectful SSA, CFG or MLIR and machine RTL/Wasm bridges are open. [#3316](https://github.com/hiloopai/silmaril-lean/pull/3316) · [#3404](https://github.com/hiloopai/silmaril-lean/pull/3404) |

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

## Remaining work in priority order

1. **Close the cyclic path from structured frontend through reversion.**
   Formalize Figure 19 admission and its relation to the repaired guard.
   Prove source-to-CFG-like admission and implement checked placement and
   extraction for nested loops, branches and shared state. Carry first-exit
   and prefix obligations through selection and reversion. The exact scalar
   and pair extractors, the checked single-loop region, and the inferred
   two-level compiler layout serve as regression cases.
2. **Formalize the general saturation and cost interfaces.** Model
   node-generating analyses and prove (4.1)–(4.4) with their hypotheses.
   Relate worklist execution and constrained selection to that model. Port
   Appendix A rule families with their definedness and language hypotheses,
   then replay the optimization examples of §§2–3 and Fig. 38. Keep the
   literal Theorem 1 counterexample and the repaired theorem side by side.
3. **Prove a separate completion-sensitive refinement.** Start with the
   discarded-failure and discarded-loop examples. Specify which returned
   values, faults and termination facts the token or trace observes before
   extending the compiler and rewrite checker. Theorem 2's existing
   successful-return implication remains the paper claim.
4. **Extend the Java and experimental coverage.** Model bytecode and the
   heap/exception behaviors needed by the historical frontend and
   linearizer, then verify the relevant translation-validation path.
   Separately pin the historical workloads, engine/solver and Soot versions,
   and rerun the §9 measurements. Full IR comorphisms for loops/effects are
   a distinct extension, with additional model and observation obligations.
