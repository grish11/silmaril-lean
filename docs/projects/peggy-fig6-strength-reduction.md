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
unit increment and Boolean negation. The reverter finds the eval and pass
leaves reached from the ordered roots through primitive operations. It uses
one leaf to identify the shared pass and reads the exit predicate from that
pass. The checker requires every reached eval to sample a carried θ at the
same pass, and every reached pass leaf to name that row. The reverter
collects all θ rows in table order and reads their typed initial and feedback
operands. Its exit schedule preserves the order and multiplicity of the
original roots.

Exactly one carried slot must initialize from the designated zero opcode
and update through the designated unary increment wired to itself.
The reverter proposes a whole-table demand rank. It propagates phase
requirements from operands for one round per row, with a strict drop
on sampling edges, then uses bounded sink ranking on edges that tie in
phase and loop counter. This admits the retained dead multiplication
that consumes an eval. The existing closed-loop checker validates the
proposed rank, boundary, and primitive schedules over the parameter,
old θ, and exit scopes. The checker retains proof that the emitted program
uses the requested opcode roles.

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
same typed input tuple used in the PEG semantics. Its assumptions are the
checked wiring and demand rank, the zero and unit-increment laws for the
clock slot, and Boolean negation of the cached exit predicate. The execution supplies the defined guard
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

## External parameters

The same entry point accepts a typed parameter list. The
[parameter scope adapter](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Parameters/Defs.lean)
loads each parameter row from the input port named by its label and
projects those bindings unchanged through each iteration. Distinct rows
can reference the same input port. The initializer may read parameters.
The guard and update may read parameters and the current θ vector, and
the update commits the complete next vector simultaneously. The exit
schedule may read parameters, eval samples, and the shared pass. At least
one output dependency must be a pass or eval leaf. The verifier checks
all four primitive schedules and rejects an initializer that tries to use
the pass before the loop.

The parameterized regression uses the same graph for zero and three
trips. Its guard compares the clock with an input limit. Its accumulator
starts at `base + delta` and adds `delta + oldClock` on each step. The
ordered outputs include a direct Boolean input, the exit count, the
sampled accumulator, and a repeated sum of that sample and `delta`.
With base 2 and delta 4 the four count outputs are `[10, 0, 6, 10]` at
limit 0 and `[25, 3, 21, 25]` at limit 3. The successful-return theorem
requires the three opcode role laws. The finite execution supplies
definedness of the scheduled work, including the exit slice.

Discovery remains limited to a single parentless loop with primitive
slices and one recognized unit counter. It collects every θ, so unsupported
slices in extra carried rows can cause rejection. Boundary and rank
discovery completeness, nested or effectful loops, and general CFG
reversion remain open for this entry point.

```sh
lake build --wfail +Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
