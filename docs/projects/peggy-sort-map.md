# Peggy signatures with variable data sorts

`Silmaril.SSA.Peggy.SortMap.inst` is the Peggy institution over signatures
that carry their own data sorts. A signature morphism consists of a function
on data sorts and an opcode map at the resulting ordered operand and result
profiles. It fixes the built-in Boolean and natural-number count sorts.
Distinct source data sorts may have the same image. The fixed-sort API
continues to use its existing signature and equation types.
[Signatures and institution](../../Silmaril/SSA/Peggy/Institution/SortMap/Thms.lean)

## Graphs and observations

`PEG.Graph.mapData` takes any typed PEG over the source alphabet and
returns the same numbered graph over the target alphabet, with mapped
types. Parameter ports, operand slots and roots are transported by
position. In particular, two argument slots remain separate even if
their types become equal. Vertices, loop keys, the loop forest and edge
roles are unchanged. Theorems give equivalence of edge and demand relations
pointwise and equivalence of structural admission. The identity,
composition and fixed-sort comparison theorems use heterogeneous
equality to align the boundary lists.
[Graph definitions](../../Silmaril/SSA/PEG/SortMap/Defs.lean) ·
[Graph theorems](../../Silmaril/SSA/PEG/SortMap/Thms.lean)

The model reduct pulls target carriers back along the sort function.
`mapDataTupleEquiv` transports a parameter assignment in either direction
by its slots, with no inverse sort function. The equation transport lemma
compares every node equation, including lazy choice, feedback, pass and
eval. Figure 11 solution uniqueness then gives pointwise denotation
transport and equality of the ordered optional roots. Bottom is
preserved at each root. Applying the tuple equivalences to both sides of
a sentence proves exact satisfaction.

The institution uses `Plain.toInst` with discrete interpretation
categories. `fixedComparison` is a comorphism out of the existing
fixed-sort institution. On each signature it uses the same sentences
and models. `map_fixed` and `reduct_fixed` identify the existing and new
actions along identity-sort arrows.
[Institution theorems](../../Silmaril/SSA/Peggy/Institution/SortMap/Thms.lean)

The fixture identifies two distinct data sorts in a guarded recurrence.
The mixed-profile step becomes addition at a repeated target sort.
Starting with the distinct input positions `2` and `9`, the ordered
roots at iteration one yield `11` and `9`. The fixture also exercises
the bundled satisfaction condition and refutes the equation that replaces
the first root with its seed.
[Fixture](../../tests/ssa/PeggySortMap.lean)

This extension uses the existing Figure 11 demand guard. It translates
sorts and primitive symbols, with the source carriers determined by
pullback. Term substitution, a conversion between arbitrary independent
carrier choices, and IR or reversion translations are outside its
contract.

```sh
lake build --wfail +Silmaril.SSA.Peggy.Institution.SortMap.Thms PeggySortMapTests PeggyInstitutionTests PeggyDialectTests PEGCoreTests
lake env leanchecker Silmaril.SSA.PEG.SortMap.Thms
lake env leanchecker Silmaril.SSA.Peggy.Institution.SortMap.Thms
lake env leanchecker tests.ssa.PeggySortMap
```
