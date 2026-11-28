# Checked discovery of a sequential PEG schedule

This step toward [Peggy §7.2–7.5](https://arxiv.org/pdf/1012.1802v3#page=41)
places candidate loop regions in an original typed PEG. The inputs are
the original graph and its ordered roots, an original demand rank,
opcode roles, a list of candidate leaves, and a search budget. A leaf
provides a checked local graph and its typed input and output interfaces.
The existing parentless unit-counter and graph-local parent/child
discoverers can construct those certificates from local graphs. A
nested-only instruction set supplies just Boolean negation.
[Discovery definitions](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Defs.lean)

## Search and checking

- Find the original parameter row for each typed input port. Try every
  supplied leaf once, choosing the order by bounded backtracking.
- A row anchor proposes a pair of local and original addresses. The
  worklist starts at the leaf’s outer pass, compares internal labels and
  propagates their ordered operand pairs. It also pairs the θ, pass and eval loop keys and follows their
  parent links. Repeated requests check the same mapping, so cyclic
  dependencies do not expand forever. The search tries additional
  anchors for local rows that the worklist did not reach.
- A local parameter terminates the walk at an available boundary row.
  The typed input projection is reconstructed from the exact references
  in that bundle. The initial bundle holds the original parameters.
  After a leaf, only its ordered output bundle supplies the next cut.
  In particular, a forwarded value must appear in that bundle. Child
  captures are internal row edges of a nested leaf, so their
  per-activation coordinates remain part of that leaf's proof.
- The final typed projection selects the original roots in their exact
  order, including repetitions. The existing `Schedule.check` checks
  the proposed plan and the original demand rank.

Each local parameter port must have a unique parameter row, every
local row must map, and every local loop key must be determined by a
mapped label or its parent chain. The search covers the supplied leaf
interfaces. It leaves candidate region generation and interface
selection on the original table as separate problems. Every attempted
leaf and row or loop worklist request spends one budget unit, with the
same budget across backtracking. `.budget` reports exhaustion.
`.invalidRank` reports a rejected rank certificate and `.parameterRows`
reports missing or nonunique original parameter rows. `.noPlan`
reports that this search returned no checked placement for the supplied
leaves. The budget measures search requests. Graph scans and final
checking have their own costs.

## Correctness and regressions

A success contains the exact `Schedule.check` equation on the original
graph. `Found.observations_of_exec` proves ordered Figure 11 return
agreement, including each required first exit and intermediate tuple.
`Found.exec_iff_observations` also constructs a successful emitted run
given the existing slice-definedness premises. Both use the leaf opcode
laws, and nested leaves require each continuing activation's child first
exit in the observation. These are the existing schedule theorems
transported through checked discovery.
[Public theorems](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Thms.lean)

The sibling regression submits the candidates in reverse order,
recovers the two-stage handoff, and executes to `[13, 3, 3, 13]`. A
different ordered root bundle executes to `[3, 13, 13, 3]`. A well-typed
guard edge to a stale input exceeds the leaf's available boundary and
is rejected. The nested regression matches a local parent/child leaf
to the original table with both rows and loop keys permuted and returns
`[4]`. The proof covers accepted schedules. General discovery
completeness and Figure 19 extraction remain outside this result.
[Sibling regressions](../../tests/ssa/PeggyEgg.lean) ·
[Nested regression](../../tests/ssa/PEGCanonicalWhile.lean)
