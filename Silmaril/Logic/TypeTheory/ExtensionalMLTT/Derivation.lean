module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Derivation

/-! # MLTT derivations from judgment hypotheses

`ECtx.JEqH` extends the source calculus with hypothesis leaves. `bind`
substitutes derivations for those leaves; `mono` extends the hypothesis set.
`empty_iff` identifies empty-theory derivability with the original `ECtx.JEq`.
-/
