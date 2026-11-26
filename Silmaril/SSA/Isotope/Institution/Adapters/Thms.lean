module

public import Silmaril.SSA.Isotope.Institution.Adapters.UpperPowerset.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.Inclusions.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.Adapters.Hierarchy

/-! # Commuting comparisons of the six exact Isotope tiers -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters

open CategoryTheory Semantics Silmaril.Logic.Institution
open LetIter.ProofRelevant.Semantics (TypeModel TyDen)
open Parallel (ParOp)

universe u v

variable {τ ε ν : Type u} [TypeFormers τ] [DecidableEq ν]
  {S : InstrSig τ ε} {Γ : Ctx ν τ}

/-- Both routes from LetSeq store the same witnesses in the parallel case sentence. -/
theorem seqCase_sentence_commutes (φ : Relational.LetSeq.Sentence S Γ) :
    Powerset.ofLetCase (Relational.seqCaseSentence φ) = (Powerset.ofLetSeq φ).ofLetPar :=
  Proofs.seqCase_sentence_commutes φ

/-- Both routes from LetCase store the same witnesses in the parallel iteration sentence. -/
theorem caseIter_sentence_commutes (φ : Relational.LetCase.Sentence S Γ) :
    Iteration.ofLetIter (Relational.caseIterSentence φ) =
      Iteration.ofLetParCase (Powerset.ofLetCase φ) :=
  Proofs.caseIter_sentence_commutes φ

/-- Along the outer paths from LetSeq, the resulting upper equation is the same. -/
theorem seqIter_sentence_commutes (φ : Relational.LetSeq.Sentence S Γ) :
    Iteration.ofLetIter (Relational.caseIterSentence (Relational.seqCaseSentence φ)) =
      Iteration.ofLetParCase ((Powerset.ofLetSeq φ).ofLetPar) := by
  rw [caseIter_sentence_commutes, seqCase_sentence_commutes]

section Lower

variable (Γ) (D : τ → Type v) [ProductModel D] [UnitModel D]
  [CoproductModel D] [EmptyModel D]

/-- The lower square commutes as corridors, including the backwards model functors. -/
theorem seqCase_corridor_commutes (pair : ParOp (SetM : Type v → Type v)) (S : InstrSig τ ε) :
    (Powerset.letSeq (D := D) Γ pair).ρ.app S ≫
        (Powerset.letParCaseInclusion (D := D) Γ pair).ρ.app S =
      (Relational.seqCaseRho Γ D).app S ≫ (Powerset.letCase (D := D) Γ pair).ρ.app S :=
  Room.hom_ext (funext fun φ => (seqCase_sentence_commutes φ).symm) rfl

end Lower

section Upper

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

attribute [local instance] LetParIter.nativeProductModel LetParIter.nativeUnitModel
  Iteration.nativeCoproductModel Iteration.nativeEmptyModel

/-- The upper square commutes as corridors at the same fixed powerset profile. -/
theorem caseIter_corridor_commutes (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (S : InstrSig τ ε) :
    (Powerset.letCase (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).ρ.app S ≫
        (UpperPowerset.letParCase hΓ pair).ρ.app S =
      (Relational.caseIterRho Γ TyDen).app S ≫ (UpperPowerset.letIter hΓ pair).ρ.app S :=
  Room.hom_ext (funext fun φ => (caseIter_sentence_commutes φ).symm) rfl

/-- The upper square commutes as bundled institution comorphisms. -/
theorem caseIter_comorphism_commutes (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) :
    (Powerset.letCase (ε := ε) (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).comp
        (UpperPowerset.letParCase (ε := ε) hΓ pair) =
      (Relational.caseIterCoHom (ε := ε) Γ TyDen).comp (UpperPowerset.letIter (ε := ε) hΓ pair) :=
  Proofs.caseIter_comorphism_commutes hΓ pair

/-- The composite routes agree on sentences, model reducts, and satisfaction. -/
theorem seqIter_corridor_commutes (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (S : InstrSig τ ε) :
    ((Powerset.letSeq (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).ρ.app S ≫
        (Powerset.letParCaseInclusion (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).ρ.app S) ≫
        (UpperPowerset.letParCase hΓ pair).ρ.app S =
      ((Relational.seqCaseRho Γ TyDen).app S ≫ (Relational.caseIterRho Γ TyDen).app S) ≫
        (UpperPowerset.letIter hΓ pair).ρ.app S :=
  Room.hom_ext (funext fun φ => (seqIter_sentence_commutes φ).symm) rfl

/-- The case route to LetParIter reflects relational satisfaction in the fixed powerset profile. -/
theorem caseIter_set_satisfaction (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (I : LetIter.ProofRelevant.Semantics.InstructionModel S.Instr τ ε SetM)
    (φ : Relational.LetCase.Sentence S Γ) :
    LetParIter.Institution.Sat (Iteration.setModel pair I) (Iteration.ofLetParCase (Powerset.ofLetCase φ)) ↔
      Relational.LetCase.Sentence.Satisfies (Iteration.setRelations I) φ := by
  rw [← caseIter_sentence_commutes, Iteration.set_satisfaction hΓ, Relational.caseIter_satisfaction]

end Upper
end Silmaril.Isotope.Institution.Adapters
