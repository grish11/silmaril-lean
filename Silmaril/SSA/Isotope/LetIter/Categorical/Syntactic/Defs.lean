module

public import Silmaril.SSA.Isotope.Bridge.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Strength.Thms

/-! # The native LetIter signature in its syntactic Freyd category -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter (Sig)
open Silmaril.Thesis.LambdaIter.Syn (SynCat mk)
open Silmaril.Thesis.LambdaIter.Syn.SynCat
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- The native signature read in the exact thesis syntax used to form the quotient. -/
abbrev signature (pe : ε) : Sig.{u} :=
  letI := Bridge.thesisTypeFormers τ
  letI := Bridge.thesisHasTy Φ τ
  letI := Bridge.thesisHasEff Φ ε
  Bridge.thesisSig τ Φ ε pe

/-- Interpret a native type as itself in the syntactic value category. -/
def valueObj (pe : ε) (A : τ) : ValueCat (signature (τ := τ) (Φ := Φ) pe) :=
  ⟨SynCat.of A⟩

/-- The syntax product and unit give the chosen Cartesian structures. The syntax
sum is compared to Mathlib's chosen coproduct by their universal properties. -/
@[instance_reducible] noncomputable def typeModel (pe : ε) :
    TypeModel τ (ValueCat (signature (τ := τ) (Φ := Φ) pe)) where
  obj := valueObj (Φ := Φ) pe
  productIso A B := Iso.refl (valueObj (Φ := Φ) pe (product A B))
  unitIso := Iso.refl (valueObj (Φ := Φ) pe (unit : τ))
  coprodIso A B := by
    let comparison := (valueCofanIsColimit (valueObj (Φ := Φ) pe A) (valueObj (Φ := Φ) pe B)).coconePointUniqueUpToIso
      (coprodIsCoprod (valueObj (Φ := Φ) pe A) (valueObj (Φ := Φ) pe B))
    exact comparison
  emptyIsInitial := valueEmptyIsInitial _

/-- A primitive instruction is represented by applying it to the input variable. -/
@[instance_reducible] noncomputable def instructionModel (pe : ε) :
    InstructionModel (values (signature (τ := τ) (Φ := Φ) pe)) (typeModel pe) Φ where
  denote f := by
    letI := Bridge.thesisTypeFormers τ
    letI := Bridge.thesisHasTy Φ τ
    exact mk (S := signature (τ := τ) (Φ := Φ) pe) (HasType.op (f := f) HasType.newest)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
