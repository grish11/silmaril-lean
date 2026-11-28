# Comparing node-generating E-PEG steps

This development uses the [append-only saturation transition](peggy-node-extension.md)
to prove (4.2) for the §5.3 zero-sample-through-θ analysis. It also states
and proves (4.3) for any pair of analyses with the required hypotheses.
The equation numbers refer to printed pp. 20–21 of arXiv:1012.1802v3.
[Paper](https://arxiv.org/pdf/1012.1802v3)

## Comparison

An [`Embedding`](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Comparison/Defs.lean)
is an injection from the old vertex numbers to the target vertex numbers
with a sort equation for each address. It preserves each old row's actual
label and ordered typed operand references, the ordered roots (including
repeated roots), and the entire loop frame. Consequently, the image is
closed under operands, including feedback reads. The target identifies
every pair identified by the source partition. This condition concerns
same-class pairs, so representative labels may change and the target may
join further pairs.

`Comparable` is existence of an embedding between packaged states.
Identity and composition give a preorder. `Step.embedding` proves
(4.1) for any append receipt, using the original indices followed by a
new last address. A general comparison can reorder the old addresses.
For paired appends, `Embedding.appendVertices` extends an arbitrary
address injection by sending the source's last address to the target's
last address. This fixes the address map for the simulation.

## Zero-sample simulation

The concrete analysis relation `ZeroSampleAnalysis zero` allows a no-op
or one actual `ZeroSample.step` at a witnessed site. The step appends
`eval ℓ (initial, zero)` and runs the existing single guarded obligation
with one merge of fuel. A witness binds exactly the same rows and
operands that the executable `ZeroSample.matchAt` checks.

Given an embedding and a source match, `ZeroSample.transport` maps its
actual eval, θ, designated literal and typed operands. The theorem
`ZeroSample.matchAt_transport` says the executable matcher at the
mapped site returns that witness. The generated label and arguments are
exactly the image of the source append. The new singleton is distinct
from every old class, so the one empty-guard obligation joins its class
with the class of the matched eval. Both runs retain their seed pairs.
Those pairs and the transported conclusion account for every pair
introduced by the smaller run. `ZeroSample.simulate` embeds the actual
finite-budget successors and specifies the resulting address map.

The rule always appends a fresh row. Even when the target contains the
same RHS and already equates it to the mapped eval, the target run
appends another RHS and joins it with the existing class. This policy
makes freshness and injectivity independent of a node-reuse decision.

The regression starts with a cyclic PEG and compares it with a larger
table that has an already-merged copy of the RHS and another row. The old
eval moves from address 4 to 6, so the embedding is not a prefix
inclusion. At address 6, the matcher appends the new RHS at 7 and merges
it with the class containing the existing RHS at 5. The smaller
successor's fresh address 5 maps to 7. The regression checks the moved
roots, both copies of the RHS and the remapped class.

## Paper claims and semantic boundary

- **(4.2)** is proved for this concrete analysis, including its no-op
  case. The proof transports a match and compares its finite merge
  results. General guarded analyses need their own transport and
  effective merge hypotheses.
- **(4.3)** follows from monotonicity of the delayed analysis and
  inflationarity of the intervening analysis. `delayed_step` states
  these premises independently. The zero-sample instantiation supplies
  its monotonicity proof.
- **(4.4)** is proved conditionally in the [normal-form theorem](peggy-normal-forms.md).
  The fresh-append zero-sample family has no stable normal form from a
  matched seed. Its retained match permits arbitrarily many duplicate rows.

The comparison is structural. The semantic certification of either
concrete transition uses `ZeroSample.holds` and `Step.sound` from the
append-only interface. In each state, assume well-founded source
demands, a valid seed partition, and the interpretation of the chosen
nullary count primitive as defined zero. The rule permits partial
initializer and feedback streams. A comparison supplies neither demand
admission for arbitrary extra target rows nor any model contract.
[Theorem header](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Comparison/Thms.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
