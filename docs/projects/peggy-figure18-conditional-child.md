# Figure 18 completion for a conditional child

`Structured.Token.Nested.Conditional.Form` extends the parent/child
compiler with a decision evaluated on the current outer store. A true
decision runs the existing projection-only capture, child while, and
loop-free commit. A false decision runs a loop-free update from the same
old outer store. The child body remains loop-free.
[Compiler](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Conditional/Defs.lean)

The lowered step joins the completion marker and each live data slot
with Figure 11 φ nodes that use the same guard. The guard and the selected
arm determine the result of each join. A skip therefore has no semantic
dependency on the child pass, its evals, or its primitives. The finite
demand rank still covers the rows and operands of both arms. An undefined
guard leaves the joined marker bottom.
[Figure 11](https://arxiv.org/pdf/1012.1802v3#page=23)

The outer data and completion evals share the ordinary outer first pass.
On a take, the child receives the current outer token at child index
zero. Its pass and completion marker are read at this outer coordinate.
The existing activation proof verifies the selected child and commit.
On a skip, the loop-free proof verifies the selected update. The returned
trace includes the emitted decision at every continuing coordinate and
requires a child first-pass and completion witness only when that
decision is true. The branch equation identifies the decision with the
source guard on the old store, and the child certificate uses the current
outer coordinate at every activation.

With the Boolean negation law, a successful original SIMPLE return
defines the same data value and a true completion marker. A defined
marker yields a successful original source execution and the matching
ordered roots. The compiler provides checked well-founded demand, and
the interpretation may have partial primitives. The unconditional
parent/child API continues to use the same shared activation proof.
[Theorems](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Token/Nested/Conditional/Thms.lean)

The countdown takes, skips, then takes again, with child lengths three
and one and result `7`. A separate fixture skips a child with a bottom
strict operation and completes. Selecting that child leaves defined data
and a bottom completion marker. [Regressions](../../tests/ssa/PEGSimple.lean)

The fragment has one outer loop and at most one unconditional child
within the selected arm. It retains projection-only captures and
loop-free child, commit, and skip paths. Bottom records the absence of
successful completion and carries no distinction between failure and
divergence.
