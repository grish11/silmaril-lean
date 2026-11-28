# Recursive Figure 18 completion for typed SIMPLE

`Structured.Token.Recursive.compile` lowers the existing typed SIMPLE
statements by structural recursion. Each statement builds an ordered
tuple with the completion marker followed by its typed output store.
The closed program observes the selected return value followed by the
marker. The compiler uses the ordinary structured PEG graph builder
and the Figure 11 semantics.
[Compiler](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Recursive/Defs.lean)

## Compositional proof

- Assignment threads the incoming marker through a strict operation that
  also demands the assigned value. Projection retains the marker when it
  discards data. Sequence passes the complete statement result into the
  next statement.
- Each conditional arm receives the old tuple. Figure 11 φ joins the
  marker and each data slot under the same condition, so the result
  depends on the selected arm. An undefined condition yields a bottom
  marker.
- A while carries the marker as an additional θ slot, seeded from the
  current activation's incoming marker. Its marker and data evals share
  the ordinary first pass. The proof follows the finite pass prefix and
  uses the next carried marker to justify each executed source step.
  Enclosing coordinates stay fixed during each activation. Even zero
  trips require a defined incoming marker.

The internal `StatementFacts` relation proves three properties at an
embedded region. A bottom incoming marker remains bottom throughout
the same enclosing scope. Successful original execution realizes all
compiled output slots. From a realized input store, defined completion
constructs an original successful execution and its realized output
store. The branch case combines the selected arm's facts. The while case
instantiates the existing scoped loop trace proof with the facts for the
recursively compiled body.
[Statement relation](../../Silmaril/Proofs/SSA/PEG/Simple/Structured/Token/Recursive/Statement.lean) ·
[Induction](../../Silmaril/Proofs/SSA/PEG/Simple/Structured/Token/Recursive/Correctness.lean)

## Admission and observations

The public correspondence covers the complete typed `Program P true`
syntax, including statements outside a loop, sibling loops, and nested
loops or conditionals. The compiler supplies a checked demand rank for
its own finite table. The interpretation supplies Boolean negation at
the compiler's designated opcode. Other primitives may be partial.
With these premises, successful original returns yield the same data
and a true marker. A defined marker reconstructs a successful original
return and determines the matching data value. Bottom represents
absence of successful completion, with failure and divergence sharing
that observation.
[Theorems](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Recursive/Thms.lean)

The recursive entry point accepts the original source of the
unconditional and conditional child fixtures. The regression also
exercises three loop levels and a discarded failing assignment followed
by a zero-trip loop. In that case the data root is defined and the marker
is bottom. The earlier shape APIs remain available for callers that use
their designated child-pass witness interfaces. This result concerns the
compiler's own tables and the finite-success fragment of Figure 18.
[Regressions](../../tests/ssa/PEGSimple.lean)
