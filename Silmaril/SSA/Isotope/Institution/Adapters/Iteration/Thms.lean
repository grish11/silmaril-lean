module

public import Silmaril.SSA.Isotope.Institution.Adapters.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Adapters.Iteration

/-! # Change-of-signature and satisfaction squares at the upper parallel tier -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.Iteration

open CategoryTheory Semantics Silmaril.Logic.Institution
open LetIter.ProofRelevant.Semantics (TypeModel TyDen CtxDen BoundDen)
open Parallel.Institution (Equation)

universe u v

variable {τ ε : Type u} [TypeFormers τ] {S T : InstrSig τ ε}
  {ν : Type u} [DecidableEq ν] {Γ : Ctx ν τ}

theorem ofLetParCase_map (f : S ⟶ T) (φ : Equation S .case Γ) :
    (ofLetParCase φ).map f = ofLetParCase (φ.map f) :=
  Proofs.ofLetParCase_map f φ

theorem ofLetIter_map (f : S ⟶ T) (φ : Relational.LetIter.Sentence S Γ) :
    (ofLetIter φ).map f = ofLetIter (Relational.LetIter.Sentence.translate f φ) :=
  Proofs.ofLetIter_map f φ

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

attribute [local instance] LetParIter.nativeProductModel LetParIter.nativeUnitModel
  nativeCoproductModel nativeEmptyModel

/-- Rebuilding an upper bound environment preserves every slot. -/
theorem nativeBound_get {n : Nat} {β : BoundCtx τ n} (ρ : BoundEnv (TyDen (τ := τ)) β) :
    BoundDen.get (nativeBound ρ) = ρ :=
  Proofs.nativeBound_get ρ

/-- The strict case-model reduct commutes with restriction of instruction signatures. -/
theorem caseModel_reduct (f : S ⟶ T) :
    LetParIter.Institution.reductFunctor f ⋙ caseModelFunctor.{u, v} =
      caseModelFunctor ⋙ Parallel.Institution.Model.reductFunctor f :=
  Proofs.caseModel_reduct f

/-- Case satisfaction agrees when every visible valuation extends to the upper context spine. -/
theorem ofLetParCase_sat (hΓ : Function.Surjective (visibleEnv.{u, v} (Γ := Γ)))
    (M : LetParIter.Institution.Model.{u, v} S) (φ : Equation S .case Γ) :
    LetParIter.Institution.Sat M (ofLetParCase φ) ↔
      ((LetParCase.observation Γ (TyDen (τ := τ))).obj S).Sat (caseModel M) φ :=
  Proofs.ofLetParCase_sat hΓ M φ

/-- Widen the exact case fragment and forget feedback on models. -/
def letParCase (hΓ : Function.Surjective (visibleEnv.{u, v} (Γ := Γ))) :
    Inst.CoHom ⟨InstrSig τ ε, LetParCase.observation Γ (TyDen (τ := τ))⟩
      ⟨InstrSig τ ε, LetParIter.Institution.inst ν⟩ where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ => ⟨ofLetParCase, caseModelFunctor, ofLetParCase_sat hΓ⟩
      naturality := fun _ _ f =>
        Room.hom_ext (funext fun φ => (ofLetParCase_map f φ).symm) (caseModel_reduct f).symm }

/-- Satisfaction of each exact equation is equality in the native sequential restriction. -/
theorem ofLetIter_sat (M : LetParIter.Institution.Model.{u, v} S)
    (φ : Relational.LetIter.Sentence S Γ) :
    LetParIter.Institution.Sat M (ofLetIter φ) ↔ IterSat M φ :=
  Proofs.ofLetIter_sat M φ

/-- The LetIter companion institution with exact sequential syntax, native sequencing
and iteration, and the same strict models as LetParIter. -/
def letIterCompanion (Γ : Ctx ν τ) : InstrSig τ ε ⥤ Room.{u, v + 1, max u (v + 1)} where
  obj S := ⟨Relational.LetIter.Sentence S Γ, Cat.of (LetParIter.Institution.Model S), IterSat⟩
  map f := ⟨Relational.LetIter.Sentence.translate f, LetParIter.Institution.reductFunctor f,
    fun M φ => (ofLetIter_sat M _).symm.trans
      ((ofLetIter_map f φ ▸ LetParIter.Institution.satisfaction f M (ofLetIter φ)).trans
        (ofLetIter_sat (M.reduct f) φ))⟩
  map_id S := by
    have h := congrArg Corridor.sen ((Relational.LetIter.institution (TyDen (τ := τ)) Γ).map_id S)
    exact Room.hom_ext h (LetParIter.Institution.reductFunctor_id S)
  map_comp f g := by
    have h := congrArg Corridor.sen ((Relational.LetIter.institution (TyDen (τ := τ)) Γ).map_comp f g)
    exact Room.hom_ext h (LetParIter.Institution.reductFunctor_comp f g)

/-- Include the exact LetIter fragment on the compatible upper model category. -/
def letIter (Γ : Ctx ν τ) :
    Inst.CoHom ⟨InstrSig τ ε, letIterCompanion.{u, v} Γ⟩
      ⟨InstrSig τ ε, LetParIter.Institution.inst ν⟩ where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ => ⟨ofLetIter, 𝟭 _, ofLetIter_sat⟩
      naturality := fun _ _ f => Room.hom_ext (funext fun φ => (ofLetIter_map f φ).symm) rfl }

/-- There are no hidden slots in the empty free context. -/
theorem visibleEnv_nil_surjective :
    Function.Surjective (visibleEnv.{u, v} (Γ := (.nil : Ctx ν τ))) :=
  Proofs.visibleEnv_nil_surjective

/-- At the actual lawful finite-success powerset model, native equality of the
embedded LetIter witnesses is equality of all successful results. -/
theorem set_satisfaction (hΓ : Function.Surjective (visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (I : LetIter.ProofRelevant.Semantics.InstructionModel S.Instr τ ε SetM)
    (φ : Relational.LetIter.Sentence S Γ) :
    LetParIter.Institution.Sat (setModel pair I) (ofLetIter φ) ↔
      Relational.LetIter.Sentence.Satisfies (setRelations I) φ :=
  Proofs.set_satisfaction hΓ pair I φ

end Silmaril.Isotope.Institution.Adapters.Iteration
