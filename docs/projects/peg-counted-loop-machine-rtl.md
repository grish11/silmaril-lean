# A checked PEG counted loop in machine RTL

The [counted-loop adapter](../../Silmaril/Machine/PEG/CountedLoop/Defs.lean)
accepts an exact typed `scf.while` shape from the
[checked PEG-to-MLIR compiler](../../Silmaril/SSA/PEG/Bridge/Theta/Region/MLIR/Thms.lean).
The input and return ABI are both three machine words in the order
`[count, left, right]`. The PEG profile decodes the count word as an unsigned
natural and interprets both data fields as 64-bit bitvectors. The three
fields occupy distinct machine pseudo-registers. `words` and `fromWords`
specify the packet representation and reject a list of the wrong arity.

Admission requires equality with the typed SCF template, including the
scope of every operand and the order of every edge. The regression
constructs the ordered PEG bundle with the existing checker, then proves
the exact compiler-image equality by reduction. The adapter specializes
that shape to machine code. The opcode interpretations must implement
word nonzero, modular decrement, and modular addition. Negation in the
source pass must compute Boolean complement.

The emitted program runs in
[`Silmaril.Machine.RTL.SSA`](../../Silmaril/Machine/CBackend/RTL/SSA/Defs.lean).
The preheader binds one word constant. The header fuses the source
`i1` nonzero test into the machine conditional on the count register.
The zero edge transfers the old bank directly to the return block.
The nonzero edge transfers it to the latch, which computes `count - 1`
and `left + right` in fresh registers. The single backedge passes
`[count - 1, right, left + right]` in parallel. The machine transfer reads
the entire argument list before binding any destination register.
The exit returns all three words and leaves memory unchanged.

The [theorems](../../Silmaril/Machine/PEG/CountedLoop/Thms.lean)
show well-formedness, finite-return agreement with the exact SCF shape,
and both directions of Figure 11 agreement for the checked PEG loop.
`returns_iff_observe_bank` compares a specific typed ABI packet and
includes equality of initial and final memory. `firstExit_of_run`
recovers the common first pass and every defined eval prefix. The
machine proof compares `Prog.runMain` with the existing SCF evaluator.
For a source budget of `k` activations, `4*k + 2` machine steps suffice
for the same finite return. The extra two steps enter the header.
Every successful machine budget can be increased to a budget of this
form, which gives reflection. Each continuing activation costs four
machine steps and a stopping activation costs two.

The [regression](../../tests/ssa/PEGStructuredTheta.lean) inspects the
latch and the first transferred register bank. It checks two backedges
from `[2, 10, 1]` to `[0, 11, 12]`, zero trips with both update
temporaries unwritten, and modular addition at the top of the word
range.

The result covers the admitted compiler image for all three-word inputs
and initial memories. A broader lowering would need instruction
selection and a verified register layout for other checked schedules
and slot profiles. The ABI uses machine pseudo-registers and the
machine runner's ordered result list. Physical register allocation,
external calling conventions, effects, traps, partial primitives and
divergence are outside this result.

```sh
lake build --wfail PEGStructuredThetaTests
```
