module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Rules.Thms
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Substitution

/-! # W syntax, judgment rules and capture-avoiding substitution

`wStepType` is the three-argument dependent induction telescope. The iota rule
passes `recChildren`, a lambda that recursively eliminates each immediate child.
`Ctx.JEqH` supports theory leaves; `Ctx.JEq` is its empty-theory specialization.
-/
