module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Examples.Thms

/-! # Ordinary W-types in object extensional MLTT

This extends the full existing grammar and every original inference rule. It
adds W formation, node introduction, dependent elimination and iota, preserving
base derivations through a proved inclusion. Its finite rule budgets support
finite-tower soundness and consistency. Unrestricted-budget derivability is
proved equivalent to the original cofinite inference rules. Indexed and mutual
families are developed in separate modules.
-/
