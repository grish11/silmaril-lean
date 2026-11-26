# Figure 6 strength reduction and SIMPLE reversion

This development checks the second rewrite in §3.1, Figure 6(c→d),
printed p. 15 of arXiv:1012.1802v3. The figure keeps the sample count
`P`, changes the sampled stream from `5 * θ₁(0, 1 + x)` to a θ with
initial value zero, and feeds that θ back through addition of five.
The paper refers to the earlier derivation in §1.2, especially scaling
through θ and distributivity over addition in (1.2) and (1.1), printed
p. 8. The general push-through-θ schema is in Appendix A.1, printed
p. 74. [Figure 6](https://arxiv.org/pdf/1012.1802v3#page=15) ·
[(1.1)–(1.2)](https://arxiv.org/pdf/1012.1802v3#page=8) ·
[Appendix A.1](https://arxiv.org/pdf/1012.1802v3#page=74)

## Matched fragment and law

The [matcher](../../Silmaril/SSA/Peggy/Worked/StrengthReduction/Defs.lean)
checks a typed count multiplication with a designated nullary factor
on the left and an actual θ on the right. The θ initializer must be
the designated nullary base. Its feedback node must be the designated
unary step with the θ itself as the operand. The worked model
interprets the unary step as `1 + x`, the factor as five, the base
as zero, and the new binary feedback as `5 + scaled`.

The interpretation contract separately certifies the defined base and
factor, the folded scaled initializer, and the equality of partial
feedback computations. The last premise says that stepping and then
scaling agrees with scaling and then applying the new addition. It
compares optional values, so a mismatch in definedness also violates
the premise. The matched nullary rows guarantee invariance at all
indices. Counts and pure operations suffice for this fragment.

`scaled_recurrence` derives the new θ equation from the original node
equations. At iteration zero, it uses the folded initializer
(`5 * 0 = 0` in the worked model). At a successor, it uses only the
preceding index and `5 * (x + 1) = 5 + 5 * x`. The proof handles both
defined and bottom predecessor samples by strict lifting.

## Checked cyclic rewrite

The executable rewrite adds a binary add row that reads the scale
address, then replaces that address's opcode and operands with the
new θ pointing back to the add row. The resulting graph has an actual
two-row feedback cycle. The initial append is acyclic relative to
the old table. The subsequent replacement, which creates the cycle,
uses its own contextual rewrite proof.

`Match.lifted_solution` proves that the appended source's streams
solve the candidate's simultaneous equations. The changed row uses
the derived recurrence and every other row keeps its equation. The
independent demand-rank check admits the actual target, and
well-founded uniqueness gives the exact ordered Figure 11 result.
The graph keeps its old counter, pass expression, eval count, and
other output dependencies. It also retains the old row table.

## Worked composition and limits

The regression starts with the cyclic Figure 6(b) fixture from
[#4171](https://github.com/hiloopai/silmaril-lean/pull/4171). It runs
the existing E-PEG code-motion match, replay and selection for (b→c),
then matches and rewrites the generated multiplication at address 8.
The resulting θ reads `[1, 10]`, and the new add reads `[6, 8]`.
The same eval samples the new θ at the original pass count.
Lean checks the final graph's rank and proves its ordered results are
`[15, 3, 3, 15]` at every index. The reachability regression confirms
that the retained original multiplication row is outside the
dependency closure of the selected roots.

A total arithmetic interpretation with an incorrect new addition
still meets the (b→c) law. It fails the strength-reduction law on
predecessor zero, where the two feedback computations return five
and six. Definedness of the operands alone would allow that mismatch.

## Executable SIMPLE counterpart of Figure 6(e)

The same worked test passes the actual result of (b→c→d) to the
[automatic closed-loop reverter](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Closed/Automatic/Thms.lean).
The call names only the graph and the instruction identities for zero,
unit increment and Boolean negation. The first ordered root identifies
the pass, and that row identifies the exit predicate. Every root must be
an eval sampling a θ at that pass or a direct reference to that same pass.
The reverter collects all θ rows in table order, reads their typed initial
and feedback operands, and looks up each sampled θ in the resulting
carried vector. Repeated output roots retain their positions.

Exactly one carried slot must initialize from the designated zero opcode
and update through the designated unary increment wired to itself.
The reverter proposes a whole-table demand rank. It propagates phase
requirements from operands for one round per row, with a strict drop
on sampling edges, then uses bounded sink ranking on edges that tie in
phase and loop counter. This admits the retained dead multiplication
that consumes an eval. The existing closed-loop checker validates the
proposed rank, the boundary and the primitive schedules over the empty
initializer scope and the old θ scope. The checker retains proof that
the emitted program uses the requested opcode roles.

The emitted syntax initializes `(x, scaled)` to `(0, 0)`, continues while
`x < 3`, and simultaneously updates `(x, scaled)` to `(x + 1, 5 + scaled)`.
On exit it projects `[scaled, x, x, scaled]`. The first and fourth values
come from the repeated scaled eval, the second from the unscaled eval,
and the third from the pass count. The checked unit recurrence makes
`x` the number of successful updates, so the pass readout needs no
additional counter. The fixture retains the unscaled recurrence because
it drives the exit and is also observed. The emitted update contains
`succ`, `five` and `add`. Inspection of the entire emitted statement finds
no multiply, including in its initializer or guard.

`Accepted.observe_of_exec` covers successful finite `Simple.Exec` on the
closed input. Its assumptions are the checked wiring and demand rank,
the zero and unit-increment laws for the clock slot, and Boolean negation
of the cached exit predicate. The execution supplies the defined guard
tests and complete simultaneous updates. Its least exit and all earlier
defined samples justify the Figure 11 evals and raw pass. The fixture
composes this theorem with the existing (b→c) replay and (c→d)
strength-reduction theorems under their rank and arithmetic-law premises.
The bounded execution returns `[15, 3, 3, 15]` with three body steps.
A bound of two is exhausted. The same roles recover a row-permuted
graph, including a changed internal slot order and relocated pass and
predicate. That program returns the same ordered tuple. An eval naming
a second pass for the same predicate and an increment reading the
wrong θ both fail extraction despite having valid demand ranks.

The supported shape is a closed, parentless single loop with nonempty
ordered eval/pass roots, one structurally recognized unit counter, and
primitive initializer, guard and update slices over the inferred scopes.
Discovery collects every θ, so unsupported slices in extra carried
rows can cause rejection. There is no completeness theorem for boundary
or rank discovery. General CFG reversion, optimizer optimality, runtime
speedup, and Java, memory, or alias behavior remain outside scope.

```sh
lake build --wfail +Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
