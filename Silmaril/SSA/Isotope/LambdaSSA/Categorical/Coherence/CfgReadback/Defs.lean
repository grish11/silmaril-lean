module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Exact coordinates of a nonempty CFG denotation witness -/

@[expose] public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)

variable {Γ : VCtx τ} {L : LCtx τ} {n : Nat}

/-- The actual contextual iterate used by the nonempty CFG graph rule. -/
noncomputable def cfgDispatchArrow (R : Fin (n + 1) → τ)
    (entry : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L)))
    (collective : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) :
    J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L) :=
  caseWithContext J (entry ≫ J.map (labelAppendSplit M (List.ofFn R) L))
    (J.map (snd (ctxObj M Γ) (labelObj M L)))
    (contextualLoop J
      (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelObjToFinite M R) ≫
        collective ≫ J.map (labelAppendSplit M (List.ofFn R) L)))

variable {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- A nonempty CFG graph witness with its selected internal label family
made explicit. The value and arrow witnesses are existential inside Prop. -/
def CfgDenotesAt (R : Fin (n + 1) → τ) (entry : Region Φ) (blocks : Fin (n + 1) → Region Φ)
    (f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)) : Prop :=
  ∃ (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L)))
    (fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn R ++ L)))
    (collective : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj (labelObj M (List.ofFn R ++ L))),
    RegionDenotes J M he fe ∧ (∀ i, RegionDenotes J M (hb i) (fb i)) ∧
      CollectiveDenotes J M Γ R L fb collective ∧
      f = cfgDispatchArrow J M R fe collective

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
