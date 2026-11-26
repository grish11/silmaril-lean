# Checked reversion of two sibling loops

`PEG.Simple.Revert.While.Siblings.check` accepts two checked parentless
loop certificates, an original typed PEG with two parentless loop keys,
a supplied row correspondence, an ordered handoff, and a demand rank for
the original graph. The local graphs can be recovered with
`Closed.Automatic.extract`. Every internal row of each local graph is
matched against the original constructor, loop key, and ordered
operands. The first stage's parameter rows must map to the original
parameter rows. Every second-stage parameter row maps to the original
reference at the selected port of the first stage's ordered outputs.
The second stage's output references must match the original roots in
order. The checked fragment uses parameter, primitive, θ, pass, and eval
rows in the local graphs.

An original input needed by the second loop is included explicitly in
the first stage's output bundle. The emitted SIMPLE runs the first
statement, projects the selected boundary ports, and runs the second
statement. The projection is the entire second input context, and the
second while binds its own local store. The handoff and final result can
each duplicate or reorder ports.

For each original iteration vector the proof fixes the other coordinate
and varies only the stage's loop coordinate. The checked rows and
parameter values then give a solution to the corresponding local
Figure 11 equations. For the second stage, the first run's observation
theorem supplies its parameter values at every original index. This
justifies using the same handoff tuple throughout the second loop's
guard, feedback, and eval prefix. The accepted rank of each graph
supplies its well-founded valuation.

`Accepted.observations_of_exec` relates an actual successful sequential
SIMPLE run to both original pass counts, the first ordered observation,
and the final ordered observation. The two certificates' zero, unit
increment, and Boolean negation laws are the semantic hypotheses.
`Accepted.exec_iff_observations` also constructs a run from both defined
first passes and both defined observation tuples under each stage's
initializer, guard, step, and finish totality. It constructs the first
run before transporting the second stage's equations. The scope is a
supplied pair of sequential parentless primitive loops connected by a
typed handoff. General sibling discovery, nesting, and effects remain
outside this result.

The PeggyEgg regression uses original input `[2, 10]`. The first loop
takes two steps and produces `[3, 10, 2, 3]`. The second takes three
steps using the first computed output as its limit and the forwarded
seed 10, and returns `[13, 3, 3, 13]`. Reducing either fuel bound
exhausts that stage. Swapping the same-type handoff ports is rejected
because the original operand provenance disagrees with the swap.

[Checker and emitter](../../Silmaril/SSA/PEG/Simple/Revert/While/Siblings/Defs.lean) ·
[Finite correspondence](../../Silmaril/SSA/PEG/Simple/Revert/While/Siblings/Thms.lean) ·
[Regression](../../tests/ssa/PeggyEgg.lean)
