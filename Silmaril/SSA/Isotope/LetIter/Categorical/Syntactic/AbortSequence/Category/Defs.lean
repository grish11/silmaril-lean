module

public import Mathlib.CategoryTheory.Quotient
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Operations.Thms

/-! # The computation category of the abort-extended LetIter presentation -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

variable (pe : ε)
local notation "S" => signature (τ := τ) (Φ := Φ) pe

/-- The relation on exact syntactic arrows induced by abort equivalence of their representatives. -/
def repairedHomRel : HomRel (SynCat S) := fun _ _ f g =>
  repairedHomClass pe f = repairedHomClass pe g

instance repairedHomCongruence : Congruence (repairedHomRel (τ := τ) (Φ := Φ) pe) where
  equivalence := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  comp_left f := fun {_ _} h => repairedHomClass_comp_congr pe (f := f) rfl h
  comp_right g h := repairedHomClass_comp_congr pe (g := g) h rfl

/-- Quotient the exact computation category by the abort-extended hom relation. -/
abbrev RepairedSynCat := CategoryTheory.Quotient (repairedHomRel (τ := τ) (Φ := Φ) pe)

/-- The projection from exact computations to abort-extended computations. -/
abbrev repairedProjection : SynCat S ⥤ RepairedSynCat (τ := τ) (Φ := Φ) pe :=
  CategoryTheory.Quotient.functor (repairedHomRel pe)

/-- Map exact value arrows into the abort-extended computation category. -/
abbrev repairedValues : ValueCat S ⥤ RepairedSynCat (τ := τ) (Φ := Φ) pe :=
  values S ⋙ repairedProjection pe

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
