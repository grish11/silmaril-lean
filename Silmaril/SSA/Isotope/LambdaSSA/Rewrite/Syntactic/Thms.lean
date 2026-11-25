module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Syntactic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Continuation
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SubstitutionObstruction
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Incompleteness

/-! # Interpretation and label substitution for the native CFG entry quotient -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Region

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

section Quotient

variable {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ}

/-- Equality of representatives in the native quotient presents exactly the CFG entry theory. -/
theorem CfgQuotient.mk_eq_iff {r s : TypedRegion (Φ := Φ) Γ L} :
    Quotient.mk (cfgSetoid Γ L) r = Quotient.mk (cfgSetoid Γ L) s ↔ CfgEquiv Γ r.val s.val L :=
  Quotient.eq

/-- Even at singleton contexts, typed label substitution can distinguish
representatives identified by the CFG entry equations. -/
theorem cfgEquiv_labelSubstitution_counterexample :
    ∃ (r s : Region Φ) (σ : Nat → Region Φ),
      CfgEquiv [(Silmaril.unit : τ)] r s [Silmaril.unit] ∧
      LSubst.HasType [(Silmaril.unit : τ)] [Silmaril.unit] [Silmaril.unit] σ ∧
      ¬ CfgEquiv [(Silmaril.unit : τ)] (r.lsubst σ) (s.lsubst σ) [Silmaril.unit] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.labelSubstitution_counterexample

end Quotient

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]
  {Γ : VCtx τ} {L : LCtx τ}

/-- Interpret a quotient class using the categorical denotation of any representative. -/
@[expose] noncomputable def CfgQuotient.denote :
    CfgQuotient (Φ := Φ) Γ L → (J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)) :=
  Quotient.lift (fun r => denoteRegion J M r.property)
    (fun r s h => CfgEquiv.sound J M h r.property s.property)

@[simp] theorem CfgQuotient.denote_mk (r : TypedRegion (Φ := Φ) Γ L) :
    CfgQuotient.denote J M (Quotient.mk (cfgSetoid Γ L) r) = denoteRegion J M r.property :=
  rfl

/-- The substituted example has equal denotations in every coherent model
and distinct classes in the CFG entry quotient. -/
theorem cfgEquiv_incomplete :
    ∃ (hr : HasType (Φ := Φ) [(Silmaril.unit : τ)]
        (.cfg (.let₁ .unit (.br 1 (.var 0))) 1 (fun _ => .let₁ .unit (.br 1 (.var 0)))) [Silmaril.unit])
      (hs : HasType (Φ := Φ) [(Silmaril.unit : τ)] (.let₁ .unit (.br 0 (.var 0))) [Silmaril.unit]),
      (¬ CfgEquiv (Φ := Φ) [(Silmaril.unit : τ)]
        (.cfg (.let₁ .unit (.br 1 (.var 0))) 1 (fun _ => .let₁ .unit (.br 1 (.var 0))))
        (.let₁ .unit (.br 0 (.var 0))) [Silmaril.unit]) ∧
      denoteRegion J M hr = denoteRegion J M hs :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unitExit_incomplete J M

end Silmaril.Isotope.LambdaSSA.Region
