# LetIter repaired relation handoff

The base is `57913ff1f0b1e1047a08edd356938490f33035e7` ([#2670](https://github.com/hiloopai/silmaril-lean/pull/2670)).
This branch is for read-only review. The proof imports the merged native `AbortEquiv`.

```sh
lake build --wfail +Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms +Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Thms +Silmaril.SSA.Isotope.Bridge.Packing.Thms
lake env lean -DwarningAsError=true handoff/letiter-repaired-relation/RepairedRelation.lean
```

- `exactEquiv_inclusion` and `thesisEqv_inclusion` admit the old exact equations on both sides of the bridge.
- `commuteAbort` derives `abort (let x = a in b) ≡ let x = a in abort b`. Its substitution theorem holds for every exactly typed simultaneous bound substitution, including both pure packing and unpacking substitutions.
- `repairedHomClass` projects an exact syntactic arrow into the hom quotient induced by native `AbortEquiv`. `repairedPacked_abort_of_exact` reifies abort when the scrutinee already reifies in the exact packed hom. `repairedPacked_effectful_closed_abort` applies this to the concrete effectful witness using the existing unit and operation lemmas.
- The hom quotient comparison here is a map on individual homs. Categorical operations and general reification or reflection still require separate proofs.
