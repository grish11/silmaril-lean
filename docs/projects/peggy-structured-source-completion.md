# Checked completion for a compiled SIMPLE while

Theorem 2 turns a successful SIMPLE run into a defined PEG return. Figure 18
shows why the converse needs completion evidence. Its unchecked PEG
can return `13` while leaving division by zero outside the return's
dependencies. The paper threads a token through the division, proposes
threading it through each loop's pass, and adds the final token as a second
output so observing both outputs demands completion.
[Theorem 2](https://arxiv.org/pdf/1012.1802v3#page=36) ·
[Figure 18 and surrounding text](https://arxiv.org/pdf/1012.1802v3#page=39)

The structured compiler already recovers a top-level while trace from a
defined Figure 11 return when the guard is defined on every store and the
whole body succeeds whenever it continues. The new converse covers the
existing top-level structured while with a loop-free body, including
assignments, projections, sequencing and lazy branches. It replaces those
global hypotheses with the following evidence for the given input:

- The original compiled PEG's designated eval has a defined result. Its
  Figure 11 meaning includes the selected slot's defined eval prefix.
- The shared pass in that same graph returns a finite count. Its Figure 11
  meaning supplies the earlier false exit flags and the final true exit flag.
- The executable `checkWhilePrefix` checks that the source guard is defined
  at each reached store and that every complete loop-free body step succeeds
  before the count. The checker leaves the Boolean decisions to the pass.
  A zero count checks the guard on the input and performs no body step.
- The interpretation implements Boolean negation at the opcode used by the
  compiler. The compiler supplies well-founded demand on the original graph.

The proof relates each checked source store to its compiled carried slots,
uses the flags to select the source continue/stop rules, and constructs
`WhileTrace` for the original source with the pass's exact count and observed
return. The trace's `exec` theorem gives the original successful SIMPLE run.
[Executable check](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Defs.lean) ·
[Converse API](../../Silmaril/SSA/PEG/Simple/Structured/Completion/Thms.lean)

The countdown regression uses a strict probe whose result is discarded.
Both inputs have a defined compiled first pass of two and return of zero,
proved from the graph's equations. The probe succeeds on one input, so the
checked prefix constructs the source run. It fails finitely on the other,
so the checker rejects it and determinism rules out a successful source
return. The zero-trip case also succeeds with the probe disabled.
[Regression](../../tests/ssa/PEGSimple.lean)

This models the extra completion obligation with a separate, input-specific
check over a certified finite prefix. The corresponding emitted marker is
available for [loop-free bodies](peggy-figure18-token.md).
Completion for discarded or nested loops and preservation of divergence or
faults remain open.
