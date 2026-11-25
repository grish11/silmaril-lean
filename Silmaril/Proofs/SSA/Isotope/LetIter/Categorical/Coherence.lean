module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Silmaril.Semantics.Categories.Thms
import Silmaril.Semantics.Elgot.Thms

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.TypingCounterexample

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

noncomputable section

private abbrev Tag := Ty Unit × Bool

local instance : TypeFormers Tag where
  product A B := (.product A.1 B.1, false)
  unit := (.unit, false)
  coprod A B := (.coprod A.1 B.1, false)
  empty := (.empty, false)

local instance : HasTy Empty Tag where
  src f := f.elim
  trg f := f.elim

local instance : HasEff Empty Unit where
  eff f := f.elim

private def interp : Ty Unit → Type
  | .base _ => Bool
  | .product A B => interp A × interp B
  | .unit => PUnit
  | .coprod A B => interp A ⊕ interp B
  | .empty => Empty

private def pairView (A B : Tag) : interp (product A B).1 ≃ interp A.1 × interp B.1 :=
  if h : A.1 = B.1 then
    if B.2 then by
      change (interp A.1 × interp B.1) ≃ interp A.1 × interp B.1
      exact (Equiv.prodComm _ _).trans
        (Equiv.prodCongr (Equiv.cast (congrArg interp h.symm)) (Equiv.cast (congrArg interp h)))
    else Equiv.refl _
  else Equiv.refl _

private abbrev J := Kleisli.Adjunction.toKleisli (ofTypeMonad Part)

@[instance_reducible] private def typeModel : TypeModel Tag Type where
  obj A := interp A.1
  productIso A B := (pairView A B).toIso
  unitIso := Iso.refl _
  coprodIso A B := (Types.binaryCoproductIso (interp A.1) (interp B.1)).symm
  emptyIsInitial := IsInitial.ofUniqueHom (fun _ => ↾Empty.elim)
    (fun X f => by ext x; exact x.elim)

local instance : InstructionModel J typeModel Empty where
  denote f := f.elim

private abbrev A : Tag := (.base (), false)
private abbrev B : Tag := (.base (), true)
private abbrev Γ : Ctx Empty Tag := .nil
private abbrev β : BoundCtx Tag 1 := .snoc .nil (product A A)
private abbrev term : LocallyNameless.Tm Empty Empty 1 := .let₂ (.bv 0) (.bv 1)

private def ordinary : LocallyNameless.Derivation Empty Γ β term A :=
  .let₂ (A := A) (B := A) .bv .bv

private def swapped : LocallyNameless.Derivation Empty Γ β term A :=
  .let₂ (A := A) (B := B) .bv .bv

private theorem denotations_differ : denote J typeModel ordinary ≠ denote J typeModel swapped := by
  intro eq
  let x : envObj typeModel Γ β := (PUnit.unit, (PUnit.unit, (false, true)))
  have h := congrArg (fun f => (f.of x : Part Bool)) eq
  simp only [ordinary, swapped, denote, ProofRelevant.Semantics.Categorical.bind] at h
  let R := envObj typeModel Γ β
  let P : Type := Bool × Bool
  let p : R ⟶ P := boundVar typeModel (Γ := Γ) (β := β) 0
  let q₁ : R ⊗ P ⟶ R ⊗ (Bool ⊗ Bool) :=
    𝟙 R ⊗ₘ (typeModel.productIso A A).hom
  let q₂ : R ⊗ P ⟶ R ⊗ (Bool ⊗ Bool) :=
    𝟙 R ⊗ₘ (typeModel.productIso A B).hom
  let s₁ : R ⊗ (Bool ⊗ Bool) ⟶ envObj typeModel Γ (.snoc (.snoc β A) A) :=
    envPairHom typeModel Γ β A A
  let s₂ : R ⊗ (Bool ⊗ Bool) ⟶ envObj typeModel Γ (.snoc (.snoc β A) B) :=
    envPairHom typeModel Γ β A B
  let r₁ : envObj typeModel Γ (.snoc (.snoc β A) A) ⟶ Bool :=
    boundVar typeModel 1
  let r₂ : envObj typeModel Γ (.snoc (.snoc β A) B) ⟶ Bool :=
    boundVar typeModel 1
  change ((ProofRelevant.Semantics.Categorical.extend J (J.map p) ≫
    J.map q₁ ≫ J.map s₁ ≫ J.map r₁).of x) =
    ((ProofRelevant.Semantics.Categorical.extend J (J.map p) ≫
    J.map q₂ ≫ J.map s₂ ≫ J.map r₂).of x) at h
  rw [extend_map J p] at h
  rw [← J.map_comp s₁ r₁, ← J.map_comp s₂ r₂,
    ← J.map_comp q₁, ← J.map_comp q₂, ← J.map_comp, ← J.map_comp] at h
  change Part.some false = Part.some true at h
  exact Bool.noConfusion (Part.some_injective h)

public theorem refinedEquationSound_fails_proof : ¬ RefinedEquationSound := by
  intro sound
  exact denotations_differ (sound J typeModel () (fun f => f.elim) ordinary swapped
    (.refl ordinary.toHasType))

end

end Silmaril.Isotope.LetIter.Semantics.Categorical.TypingCounterexample
