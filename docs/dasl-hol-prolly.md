# Named HOL judgments over Prolly assumption sets

Import `Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Assumptions.Thms` for
`HOL.Prolly.derives` and `HOL.Prolly.entails` (under `Silmaril.ProofFormats.DaslSyntax`).
Prolly block roots and DASL conclusion roots are abstract names. Their readers
are supplied independently. Keys are reversible HOL term labels, not addresses.

`HOL.Prolly.readAssumptions` requires a complete bounded scan and canonical
decoding of every key. `assumptions_iff_read` characterizes the lifted finite-set
relation exactly by a successful read. `assumptions_sound` identifies the keys
of a canonical build given a stored witness, a binding reference and a sound
reader; it does not guarantee that the reader finds all blocks.

With a binding conclusion store and a named term witness, `derives_iff_kernel`
and `entails_iff_semantic` recover the original HOL judgments. With an additional
named assumption list that represents the same finite set, `derives_iff_list`
and `entails_iff_list` show that the presentations agree for those roots. List
order and duplicates do not change the hypothesis set. This is not a claim about
ordered HOL typing contexts, or an equivalence of provability and validity.

An error (including a missing block or too little fuel) supplies no finite
expansion, not an empty set or a refutation. Use the `Except` result of
`readAssumptions` to retain this distinction; there is no proof search or
decision procedure for entailment here. A missing conclusion witness also does
not refute a judgment. No CID allocation, hash injectivity or wire validation is
assumed by the bridge.

```sh
lake build --wfail +Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Assumptions.Thms +Mathlib.Tactic.FinCases
lake env lean -DwarningAsError=true --run tests/formats/DaslHOLProlly.lean
```

The regression runs the linked scan with a present child, a missing child,
insufficient fuel, and an invalid term key. Lean also checks the named HOL
derivation and entailment from a successful-read witness, with duplicate
assumptions on the list side.
