# Infer sequential sibling boundaries from PEG dependencies

`Schedule.Automatic.Siblings.discover` takes an original typed PEG, the
unit-counter opcode roles, a demand rank, and a schedule search budget.
It infers the cut and export references, then uses the checked leaf
and schedule pipeline from #4882. This is a conservative placement
heuristic for [§7.2–7.5](https://arxiv.org/pdf/1012.1802v3#page=41).
[Graph-only entry](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Siblings/Defs.lean)

## Inferring the boundaries

- Collect every loop key with a labelled row and require each of those
  keys to be parentless. For each row, collect the loop labels in its
  complete operand closure. A loop depends on each other key found
  through one of its labelled rows. Order the loops by those
  dependencies, breaking ties by original loop ID, and reject cycles
  between keys.
- Assign a row with loop dependencies to the latest loop in that
  order that it depends on. Computations with no loop dependency can
  remain local to a consuming leaf. Take parameters and rows assigned
  to earlier regions as boundary leaves.
- Work backward from the original roots. At each stage, export the
  required rows, including values from earlier stages that must be
  forwarded. Close the exports and the stage's loop-labelled rows at
  the boundary leaves. The encountered leaves are the required inputs
  of that stage and become exports of the preceding stage. Every
  participating loop must contribute an owned export.
- Use original row order for unique input and export store slots. The
  schedule's final typed projection reads the original roots in
  order, so one exported slot can appear multiple times in the
  return.

An export whose operand closure reaches a live θ before a pass or eval
is rejected. This is a structural test for potential readouts. The
leaf checker still validates the shared pass, guard, update, readout
slices, and cut wiring. Parent/child captures stay under the separate
nested region checker and its per-activation coordinates.

The heuristic considers all loop-labelled rows, including unused
ones. A dead loop with no export, a cycle between loop dependencies,
or a scope outside the parentless model can therefore reject.
Coverage is limited to graphs accepted by this heuristic and the leaf
checkers. The supplied budget counts attempts in the existing
schedule order search. Computing finite closures and
checking leaves have separate costs.
[Checked cut synthesis](peggy-sequential-cut-leaves.md)

## Finite-return theorem and regressions

Every success carries the equation for `Schedule.check` on the original
graph. Given the opcode laws for zero, unit tick, and Boolean negation,
`Found.observations_of_exec` uses a successful emitted SIMPLE run to
prove the original Figure 11 first exits, boundary tuples, and ordered
return. The converse `Found.exec_iff_observations` requires those defined
first exits and observations and totality of the four checked
unit-counter slices on defined input stores. The checked original
demand rank supplies well-founded evaluation in both directions.
[Checker equation](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Siblings/Thms.lean) ·
[Finite-return theorems](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Thms.lean)

The sibling fixture recovers the first loop's limit-producing export
and forwards a function parameter needed by the second loop. It runs
from the graph alone and returns `[13, 3, 3, 13]`. Swapping the loop IDs
and changing the ordered roots returns `[3, 13, 13, 3]`. A well-typed,
ranked dependency on the live sibling θ is rejected separately from
schedule budget exhaustion.
[Regressions](../../tests/ssa/PeggyEgg.lean)
