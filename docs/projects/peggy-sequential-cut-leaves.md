# Checked leaves from original PEG cuts

This [§7.2–7.5](https://arxiv.org/pdf/1012.1802v3#page=41) step removes
local graphs and leaf certificates from the caller's inputs to
sequential reversion. `Schedule.Automatic.Cuts.discover` takes the
original typed PEG, an original demand rank, opcode roles, a list of
candidate boundaries in any order, and an order-search budget. Each
boundary supplies typed input cut references and ordered exported
references in the original graph.
[Entry point](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Cuts/Defs.lean)

## Synthesis and admission

1. Start from the exported references and follow the ordered operands,
   including θ feedback and eval's pass operand. Treat each input cut
   as a parameter of the local graph and stop traversal there. Include
   even unused cut inputs so that the local parameter order is fixed.
2. Recover one parentless loop key, or one parentless key and its child
   with a singleton output. Retain all rows labelled by those keys
   and close their dependencies at the same cuts. This keeps a child's
   full exit bundle even if an outer update uses only some of it.
3. Densely number local rows and loop keys, preserve the original parent
   links, and reuse checked projection wiring for every operand and
   ordered root. For a nested leaf, restrict the original rank's row
   phases and keep only counters with retained keys. The existing
   nested recognizer checks this local rank. The unit-counter recognizer
   infers and checks its own local rank.
4. Run the existing leaf recognizers and then `Stage.check` with the
   exact original mapping. Each successful `CheckedCut` records that
   the resulting input and output references equal its supplied
   boundary. Feed these fixed placements to the existing schedule
   order search. Once the typed handoffs and final projection line up,
   `Schedule.check` checks the whole plan on the original graph.

The checker requires distinct input references. Each selected
dependency must stay within the chosen loop keys or stop at a supplied
cut. The caller supplies candidate boundaries and the recognizers
determine their support. The ordered output tuple at each stage
supplies all values forwarded to the next. Nested captures remain
internal dependencies of their own activation. They are still checked
by the nested recognizer under the enclosing old store.

An unsupported boundary reports its candidate index and the reason,
including coverage, loop shape or a rejected leaf check. A schedule
error distinguishes an invalid rank, original parameter rows, no
placement order under the given interfaces, and exhausted search
budget. The budget counts attempted stage choices, including
backtracking. Computing the finite cut closures and running the
leaf checkers are separate costs. This entry point covers the supplied
scope interfaces. Candidate boundary inference and general Figure 19
completeness remain separate.
[Typed schedule discovery](peggy-sequential-schedule-discovery.md)

## Finite execution

A successful result contains the original `Schedule.check` equation.
`Found.observations_of_exec` proves that a successful finite emitted
SIMPLE run with the given typed input has matching ordered Figure 11
root and boundary observations and the stage first exits. The
unit-counter stages require zero, unit tick and Boolean negation.
The parent/child stages require Boolean negation. The forward direction
uses the actual successful run and requires those opcode laws.

`Found.exec_iff_observations` constructs a run from the same ordered
observations if the four unit-counter slices are total and the nested
slices are defined on the specified realizable stores. It requires each
stage's original first exit and, for a nested stage, a finite child
first exit at every continuing outer activation. The well-founded
original valuation comes from the checked original rank. The result
concerns successful finite execution.
[Checker equation](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Cuts/Thms.lean) ·
[Finite-return theorems](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Automatic/Thms.lean)

The sibling fixture derives both leaves from boundaries submitted in
reverse order. The first loop's result supplies the second loop's
limit, and the emitted schedule returns `[13, 3, 3, 13]`. Reordered
and repeated original roots return `[3, 13, 13, 3]`. A stale guard
dependency fails coverage, while an insufficient order budget reports
budget exhaustion on the valid graph. The nested fixture derives a
leaf on a table with renumbered rows and loop keys and returns `[4]`.
[Siblings](../../tests/ssa/PeggyEgg.lean) ·
[Parent and child](../../tests/ssa/PEGCanonicalWhile.lean)
