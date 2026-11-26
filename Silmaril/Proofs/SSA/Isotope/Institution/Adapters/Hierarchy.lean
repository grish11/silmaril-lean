module

public import Silmaril.SSA.Isotope.Institution.Adapters.UpperPowerset.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.Inclusions.Thms
import Silmaril.SSA.Isotope.Parallel.Hierarchy.Thms

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.Proofs

open CategoryTheory Semantics Silmaril.Logic.Institution
open LetIter.ProofRelevant.Semantics (TypeModel TyDen)
open Parallel (Derivation)
open Parallel.Institution (Equation)
open LetParIter.Institution (Expr)

universe u v

variable {τ ε ν : Type u} [TypeFormers τ] [DecidableEq ν]
  {S : InstrSig τ ε} {Γ : Ctx ν τ}

theorem seqCase_sentence_commutes (φ : Relational.LetSeq.Sentence S Γ) :
    Powerset.ofLetCase (Relational.seqCaseSentence φ) = (Powerset.ofLetSeq φ).ofLetPar := by
  rw [Relational.seqCaseSentence_eq]
  let equation (l r : (a : LetParCase.Tm ν S.Instr φ.1.depth) ×
      Derivation S.Instr Γ φ.1.bound a φ.1.result) : Equation S .case Γ :=
    ⟨φ.1.depth, φ.1.bound, φ.1.result, l.1, r.1, l.2, r.2⟩
  exact congrArg₂ equation (Parallel.Hierarchy.seqCaseDerivation_commutes φ.2.1.2)
    (Parallel.Hierarchy.seqCaseDerivation_commutes φ.2.2.2)

theorem caseIter_sentence_commutes (φ : Relational.LetCase.Sentence S Γ) :
    Iteration.ofLetIter (Relational.caseIterSentence φ) =
      Iteration.ofLetParCase (Powerset.ofLetCase φ) := by
  rw [Relational.caseIterSentence_eq]
  let equation (l r : (a : LetParIter.Tm ν S.Instr φ.1.depth) ×
      Derivation S.Instr Γ φ.1.bound a φ.1.result) : LetParIter.Institution.Sentence S ν :=
    ⟨Γ, φ.1.depth, φ.1.bound, φ.1.result, ⟨l.1, l.2⟩, ⟨r.1, r.2⟩⟩
  exact congrArg₂ equation (Parallel.Hierarchy.caseIterDerivation_commutes φ.2.1.2)
    (Parallel.Hierarchy.caseIterDerivation_commutes φ.2.2.2)

theorem seqIter_sentence_commutes (φ : Relational.LetSeq.Sentence S Γ) :
    Iteration.ofLetIter (Relational.caseIterSentence (Relational.seqCaseSentence φ)) =
      Iteration.ofLetParCase ((Powerset.ofLetSeq φ).ofLetPar) := by
  rw [caseIter_sentence_commutes, seqCase_sentence_commutes]

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

attribute [local instance] LetParIter.nativeProductModel LetParIter.nativeUnitModel
  Iteration.nativeCoproductModel Iteration.nativeEmptyModel

/-- The upper square commutes as corridors at the same fixed powerset profile. -/
private theorem caseIter_corridor_commutes (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
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
      (Relational.caseIterCoHom (ε := ε) Γ TyDen).comp (UpperPowerset.letIter (ε := ε) hΓ pair) := by
  let left := (Powerset.letCase (ε := ε) (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).comp
    (UpperPowerset.letParCase (ε := ε) hΓ pair)
  let right := (Relational.caseIterCoHom (ε := ε) Γ TyDen).comp (UpperPowerset.letIter (ε := ε) hΓ pair)
  change left = right
  refine Inst.CoHom.ext (f := left) (g := right) rfl ?_
  change left.ρ ≫ 𝟙 _ = right.ρ
  rw [Category.comp_id]
  ext : 1
  funext S
  simp only [left, right, Inst.CoHom.comp, Relational.caseIterCoHom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app, Category.comp_id]
  exact caseIter_corridor_commutes hΓ pair S

theorem seqIter_corridor_commutes (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (S : InstrSig τ ε) :
    ((Powerset.letSeq (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).ρ.app S ≫
        (Powerset.letParCaseInclusion (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).ρ.app S) ≫
        (UpperPowerset.letParCase hΓ pair).ρ.app S =
      ((Relational.seqCaseRho Γ TyDen).app S ≫ (Relational.caseIterRho Γ TyDen).app S) ≫
        (UpperPowerset.letIter hΓ pair).ρ.app S :=
  Room.hom_ext (funext fun φ => (seqIter_sentence_commutes φ).symm) rfl

theorem seqIter_comorphism_commutes (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) :
    ((Powerset.letSeq (ε := ε) (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).comp
        (Powerset.letParCaseInclusion (ε := ε) (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b))).comp
        (UpperPowerset.letParCase (ε := ε) hΓ pair) =
      (Relational.seqIterCoHom (ε := ε) Γ TyDen).comp (UpperPowerset.letIter (ε := ε) hΓ pair) := by
  let left := ((Powerset.letSeq (ε := ε) (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b)).comp
    (Powerset.letParCaseInclusion (ε := ε) (D := TyDen (τ := τ)) Γ (fun a b => pair.pair a b))).comp
    (UpperPowerset.letParCase (ε := ε) hΓ pair)
  let right := (Relational.seqIterCoHom (ε := ε) Γ TyDen).comp (UpperPowerset.letIter (ε := ε) hΓ pair)
  change left = right
  refine Inst.CoHom.ext (f := left) (g := right) rfl ?_
  change left.ρ ≫ 𝟙 _ = right.ρ
  rw [Category.comp_id]
  ext : 1
  funext S
  simp only [left, right, Inst.CoHom.comp, Relational.seqIterCoHom, Relational.seqCaseCoHom,
    Relational.caseIterCoHom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Category.comp_id]
  exact seqIter_corridor_commutes hΓ pair S

end Silmaril.Isotope.Institution.Adapters.Proofs
