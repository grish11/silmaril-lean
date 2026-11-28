# Cyclic PEG self-feedback elimination

[`Optimizer.Cyclic.optimize`](../../Silmaril/SSA/Peggy/Optimizer/Cyclic/Defs.lean)
accepts a typed, nonempty PEG table with one loop. It searches for a θ whose
feedback operand is its own address and whose initializer is a distinct
zero-input node. At iteration zero θ reads the initializer. At each successor
iteration θ reads its own previous value. A parameter or nullary primitive
has no index-dependent operands, so its stream is invariant in the loop.
The invariant holds for partial nullary primitives even when they return
bottom. The implementation uses the guarded Figure 11 invariance and
self-feedback theorems for this rule.

## Admission and certificate

1. The source may contain parameters, primitive applications, φ and θ. The
   sole loop must have no parent. Admission estimates a nonfeedback phase
   with one synchronous update per row and checks all nonfeedback edges
   for descent. It independently checks native demands against the
   lexicographic rank of the loop counter and the phase. These checks
   establish the paper's structural `WellFormed` guard and well-founded
   demand. The profile excludes pass and eval.
2. The search visits each numbered row at most once. The matched row
   supplies one guarded equation to the [finite saturation kernel](peggy-saturation.md),
   starting from singleton classes. Literal self feedback discharges the
   class guard in the initial partition. The initializer test supplies the
   semantic invariance premise. `Match.rule_holds` and `Match.classes_valid`
   justify the merge for every interpretation and input.
3. Extraction deletes the matched row, compacts the addresses, and redirects
   its uses and output occurrences to the initializer. All other rows keep
   their original typed labels. The target goes through the same structural
   and demand checks on its own table. Extraction builds each selection
   witness from the retained source row and its redirected arguments. The
   [selection kernel](peggy-epeg.md) checks the classes of corresponding
   operands and ordered roots, then derives the target's Figure 11 equations.

[`Result.sound`](../../Silmaril/SSA/Peggy/Optimizer/Cyclic/Thms.lean)
equates the ordered tuples of partial Figure 11 results at every index,
under the same primitive interpretation and ordered input tuple. Repeated
roots and bottom are preserved. Primitive applications retain their strict
semantics, and φ retains its demand for only the selected arm.

## Scope and regression

The optimizer returns the first candidate that passes all checks. Every
success reduces stored row count by one, counting shared rows once. The pass
does not repeat the search on the target, remove unrelated dead rows, or
compare global costs. Matching is limited to literal self feedback with a
leaf initializer, and saturation has one ground obligation with one merge
of fuel. Nested loops, arbitrary invariant expressions, class-based matching,
node-generating saturation, and reversion to an imperative language remain
outside this pass.

The [regression](../../tests/ssa/PeggyEgg.lean) compacts seven rows to six,
redirecting shared uses and two ordered root occurrences while retaining a
live θ/successor counting cycle. A partial primitive initializer also
passes, and its self-feedback stream is proved bottom at iteration one.
An admitted near miss uses the live counter as initializer. The matcher
rejects it, and at iteration one its self-feedback row still denotes zero
while the initializer denotes one.

## Checked cyclic PEG-to-SIMPLE path

`SimpleValidation.Cyclic.optimize` takes a numbered one-loop PEG with
one designated output. The original optimizer's structural admission
excludes eval and pass. The cyclic SIMPLE path instead infers and checks
the single-loop demand rank with separate eval and pass phases. It uses
the same matcher, guarded saturation, compaction, ordered root check
and row replay for the first candidate that passes replay. The replay
independently checks a rank on the compacted table. Failed source
ranking, absence of a replay-checked rewrite, and rejected SIMPLE
reversion are distinct outcomes.

The compacted table must pass the graph-only single-loop region
reverter. That checker needs one parameter-backed θ per carried slot
and scope-closed primitive guard and update schedules. A redundant θ
with a nullary primitive initializer can disappear while leaving that
boundary intact. Redirecting a live use to a raw parameter outside the
carried scope can pass replay and still fail reversion.

The return theorem uses the source and target ranks and the replay
receipt to equate the Figure 11 observations. It then uses the region
theorem under guard and full-update totality and the negation law. The
fixture compiles a top-level SIMPLE while and inserts a redundant θ on
its decrement operand. The executable check discovers the rewrite and
runs the emitted SIMPLE for three iterations, returning `2`. A
concrete replay receipt proves that compaction restores the compiler
table and the original PEG's defined observation is also `2`. The
insertion is specific to the PEG-input fixture.
[Cyclic PEG-to-SIMPLE API](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Thms.lean) ·
[Fixture](../../tests/ssa/PeggySimpleValidation.lean)

## Checked SIMPLE source entry point

`SimpleValidation.Cyclic.Source.optimize` takes a typed top-level
`WhileProgram`, with a loop-free body and a designated return slot.
It uses the single-loop SIMPLE compiler, whose demand rank has a
general proof, and checks that rank on the emitted table. It discovers
and replays one self-feedback elimination on the actual compiler
output. The compiler's typed guard, update, eval and pass references
are redirected through the replay's row compaction. The region
checker verifies the redirected boundary, target rank and schedules.

A feedback slot can disappear when the source body passes that slot
through unchanged. The reverter permits an invariant slot only when
its current and next references equal the initial parameter for the
same port. The emitted SIMPLE uses an identity update for that slot
while the other slots update simultaneously. An eval that selects the
invariant slot still observes it at the loop's first pass.

Lean proves that each successful source return gives the same
successful return in any accepted output on the same input. The proof
uses the source compiler theorem, the checked replay and the existing
reversion theorem. Its premises are totality of the accepted guard
and whole update schedule, and the Boolean negation law for the
shared opcode. Acceptance succeeds in the fixture where a changing
counter reads an unchanged decrement slot. With no literal self
feedback the entry point rejects at discovery. A demanded φ or
another unsupported operand can still fail the primitive scheduler
after successful replay. The theorem covers successful returns in this
checked top-level fragment.
[SIMPLE-to-SIMPLE API](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Source/Thms.lean) ·
[Source regressions](../../tests/ssa/PeggySimpleValidation.lean)

```sh
lake build --wfail PEGCoreTests PEGRulesTests PeggyEggTests PeggySimpleValidationTests
lake env leanchecker --fresh Silmaril.SSA.Peggy.Optimizer.Cyclic.Thms
lake env leanchecker tests.ssa.PeggyEgg
lake env leanchecker --fresh Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```
