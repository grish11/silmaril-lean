# Typed sequential reversion of PEG regions

In [Peggy §7](https://arxiv.org/pdf/1012.1802v3#page=40), reversion
places PEG computations into executable control flow. This slice
composes already checked loop regions across typed, ordered boundaries.
It uses the original Figure 11 graph for all observations and emits
ordinary typed SIMPLE projections, sequential statements, and the
existing checked while bodies.

## Checking a schedule

A `Plan` is a finite sequence of stages with a final projection. Each
stage declares its own checked region, typed input and output stores,
an address for every local row, and a mapping for every local loop key.
The leaf certificates are those of the parentless primitive unit-counter
region and the graph-local parent/child region. The second emits a
one-slot store containing the nested program's declared return.

The checker compares the entire local table against the original graph.
It validates typed row labels and ordered operands, injective loop-key
mappings within each stage, and exact parent links. A local parameter
row must map to the specified port of the preceding stage's output
bundle. At entry, each supplied reference must be the matching original
parameter row. At exit, the final projected references must equal the
original roots in order. Projections can reorder, duplicate or discard
ports. Forwarded values must be present in the preceding output bundle.
The checker also checks a supplied demand rank for the original table.
Local ranks and loop boundaries come from the checked leaf certificates.
[Definitions](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Defs.lean)

## Finite-return correspondence

`Stage.pull_solves` transports the original Figure 11 equations to a
stage. It fixes unmapped coordinates at the enclosing index, substitutes
local coordinates via the checked loop-key map, and preserves the
parameter equations when the cut inputs are defined with the same typed
values at every index. The setting of local coordinates commutes with
the corresponding original index updates, so θ, pass and eval follow
the original edges. The sequential proof derives the cut premise at
entry from parameter rows and at every later stage from the preceding
successful execution. Each nested leaf uses its own parent/child proof
of reset, current captures, and commit from the child's exit.

`Accepted.observations_of_exec` supplies the stage exits and intermediate
stores and proves that the original ordered roots equal the successful
SIMPLE return. The single-loop leaf requires its zero, unit tick and
Boolean negation laws. The nested leaf requires Boolean negation and
records a child first exit for each continuing outer activation.

`Accepted.exec_iff_observations` also constructs an emitted SIMPLE
run from those PEG observations. That direction needs the single-loop
leaf's four total slices and the nested leaf's defined slices on its
realized stores. Defined primitive slices do not supply a child first
exit. The converse first constructs a stage execution and derives the
uniform handoff before proving that the next stage runs.
[Public theorems](../../Silmaril/SSA/PEG/Simple/Revert/Schedule/Thms.lean)

The regressions exercise the existing two-sibling handoff and the
two-then-one parent/child activation through the same checker. The
sibling returns `[13, 3, 3, 13]` and rejects swapped same-type boundary
ports. The parent/child returns `[4]` and rejects an initializer wired
to a stale function input. This schedule covers sequential boundaries
whose completed outputs are uniform in loop coordinates. It needs
supplied local certificates and mappings. Branch placement, arbitrary
nesting, discovery, fusion, and general Figure 19 extraction remain
separate obligations.
[Sibling regression](../../tests/ssa/PeggyEgg.lean) ·
[Nested regression](../../tests/ssa/PEGCanonicalWhile.lean)
