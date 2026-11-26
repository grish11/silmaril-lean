# Graph-local discovery for checked parent/child reversion

[`Nested.Region.Automatic.extract`](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Automatic/Defs.lean)
takes a typed PEG with a singleton designated root tuple, a demand rank for
that graph, and a typed Boolean negation opcode. It recovers a candidate
descriptor and runs the existing graph-local `Nested.Region.check` on the
original graph. The returned certificate supplies the existing nested SIMPLE
program and its executable interpreter.

## Discovered boundary and schedules

- The designated root must be an outer `eval`. Its loop key and count operand
  identify the parentless loop and its pass. The forest must identify a unique
  direct child, and the graph must have a unique `pass` row for that child.
  Discovery reads each pass's exit flag from its operand.
- For each typed input port, discovery finds exactly one outer `θ` initialized
  by that parameter. These slots must account for all outer `θ` rows. Their
  input-port order defines the outer store. The designated `eval` selects the
  returned slot, and the `θ` feedback operands give the outer update roots.
- The child must have a nonempty bundle of `eval` rows on its shared pass,
  with one distinct projection per child `θ` and no unprojected child slot.
  Their row order defines the typed child store. The corresponding `θ`
  operands supply the capture initializers and feedback roots.
- The existing checker checks the boundary and rank, then infers and replays
  the primitive schedules. Child initialization can read the current outer
  store. The child guard and feedback can read the child store and current
  outer store. The outer commit can read the child exit ports and the old
  outer store. The typed tuple updates retain simultaneous old-store semantics.

Discovery uses the root, forest, labels, and ordered operands. Row numbers
serve to enumerate candidates and order child slots. The supplied rank must
match the input graph. The original and relocated regressions require only
the graph, rank, and negation opcode. They run child activations of lengths
two and one and return `4` with input `(0, 2)`. Relocation permutes both loop
keys and row addresses and reverses the order of the child slots. A well-ranked
stale capture still yields a candidate, which the schedule checker rejects.
A child projection using a different count operand fails discovery.

## Finite-return contract

[`Recovered.observe_of_returns`](../../Silmaril/SSA/PEG/Simple/Revert/While/Nested/Region/Automatic/Thms.lean)
uses the configured opcode's negation law to relate any successful emitted
SIMPLE return to the original PEG's Figure 11 observation on the same input.
`Recovered.returns_iff_exits` reuses the checked region's finite correspondence
under its `DefinedSlices` premise, including execution of the full commit.
The PEG side requires the outer first exit, a defined child first exit during
each continuing outer iteration, and the designated observation. Total
primitives can discharge the slice premise. The child first exits remain
explicit witnesses. Zero outer trips require no child first exit.

The entry point covers the existing primitive-slice two-level region with the
bundle and initializer conventions above. Its guarantees concern successful
finite returns. Recognition completeness, arbitrary loop forests, and effects
are outside this result.
