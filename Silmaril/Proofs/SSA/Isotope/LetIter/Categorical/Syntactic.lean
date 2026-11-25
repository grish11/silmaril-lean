module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Purity.Thms

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn.SynCat

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

theorem valueInl_coprodIso_proof (pe : ε) (A B : τ) :
    (valueCofan (valueObj (Φ := Φ) pe A) (valueObj pe B)).inl ≫
      ((typeModel (Φ := Φ) pe).coprodIso A B).hom = coprod.inl := by
  exact (valueCofanIsColimit (valueObj (Φ := Φ) pe A) (valueObj pe B))
    |>.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (valueObj (Φ := Φ) pe A) (valueObj pe B))
      ⟨WalkingPair.left⟩

theorem valueInr_coprodIso_proof (pe : ε) (A B : τ) :
    (valueCofan (valueObj (Φ := Φ) pe A) (valueObj pe B)).inr ≫
      ((typeModel (Φ := Φ) pe).coprodIso A B).hom = coprod.inr := by
  exact (valueCofanIsColimit (valueObj (Φ := Φ) pe A) (valueObj pe B))
    |>.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod (valueObj (Φ := Φ) pe A) (valueObj pe B))
      ⟨WalkingPair.right⟩

theorem map_coprodIso_proof (pe : ε) (A B : τ) :
    let J := values (signature (τ := τ) (Φ := Φ) pe)
    J.map ((typeModel (Φ := Φ) pe).coprodIso A B).hom ≫
      inv (coprodComparison J (valueObj pe A) (valueObj pe B)) =
        (copIso (J.obj (valueObj pe A)) (J.obj (valueObj pe B))).hom := by
  let J := values (signature (τ := τ) (Φ := Φ) pe)
  let X := valueObj (Φ := Φ) pe A
  let Y := valueObj (Φ := Φ) pe B
  let i : (valueCofan X Y).pt ⟶ X ⨿ Y := ((typeModel (Φ := Φ) pe).coprodIso A B).hom
  let c := inv (coprodComparison J X Y)
  let k := J.map i ≫ c
  change k = (copIso (J.obj X) (J.obj Y)).hom
  have hl : injl (J.obj X) (J.obj Y) ≫ k = coprod.inl := by
    change J.map (valueCofan X Y).inl ≫ J.map i ≫ c = _
    rw [← Category.assoc, ← J.map_comp]
    have e : (valueCofan X Y).inl ≫ i = coprod.inl := valueInl_coprodIso_proof pe A B
    rw [e]
    exact map_inl_inv_coprodComparison J
  have hr : injr (J.obj X) (J.obj Y) ≫ k = coprod.inr := by
    change J.map (valueCofan X Y).inr ≫ J.map i ≫ c = _
    rw [← Category.assoc, ← J.map_comp]
    have e : (valueCofan X Y).inr ≫ i = coprod.inr := valueInr_coprodIso_proof pe A B
    rw [e]
    exact map_inr_inv_coprodComparison J
  have e := desc_uniq (copIso (J.obj X) (J.obj Y)).hom
  rw [injl_copIso_hom, injr_copIso_hom] at e
  exact (desc_uniq k).trans ((congrArg₂ desc hl hr).trans e.symm)

theorem boundObj_eq_proof (pe : ε) {n : Nat} (β : BoundCtx τ n) :
    boundObj (typeModel (Φ := Φ) pe) β =
      valueObj pe (packType (S := signature (τ := τ) (Φ := Φ) pe) (Bridge.BoundCtx.toThesis β)) := by
  induction β with
  | nil => rfl
  | snoc β A ih =>
    exact congrArg (fun X => X ⊗ valueObj (Φ := Φ) pe A) ih

theorem instruction_isPure_proof (pe : ε) (f : Φ) (hf : IsPure pe f) :
    IsPureMor ((instructionModel (τ := τ) pe).denote f) := by
  let _ := Bridge.thesisHasEff Φ ε
  exact ⟨_, _, .op hf .bv, rfl⟩

theorem denote_isPure_proof {ν : Type u} [DecidableEq ν] (pe : ε)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : LocallyNameless.Tm ν Φ n} {A : τ}
    (d : LocallyNameless.Derivation Φ Γ β t A) (h : LocallyNameless.Pure pe t) :
    letI := instructionModel (τ := τ) (Φ := Φ) pe
    IsPureMor (denote (values (signature (τ := τ) (Φ := Φ) pe)) (typeModel pe) d) := by
  let _ := instructionModel (τ := τ) (Φ := Φ) pe
  let J := values (signature (τ := τ) (Φ := Φ) pe)
  obtain ⟨p, hp⟩ := denote_pure_factor J (typeModel pe)
    (fun f hf => ⟨⟨_, instruction_isPure_proof pe f hf⟩, rfl⟩) d h
  rw [hp]
  exact p.property

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
