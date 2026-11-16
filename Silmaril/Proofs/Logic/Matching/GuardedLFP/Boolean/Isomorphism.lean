module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Boolean.Truth

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Boolean
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature} {M N : FirstOrderLFP.Model S}

theorem iso_lfp (e : M.toStructure ≅ N.toStructure) {r k : Nat}
    {P' : Fin (r+1) → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool}
    {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Boolean.Formula S P' Δ (Fin.cases true σ))
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv M Δ) (η : FirstOrderLFP.RelEnv N P'),
      θ ∈ body.denote M (pullRelations e η) ↔ envEquiv e Δ θ ∈ body.denote N η)
    (v : FirstOrderLFP.ObjEnv M Γ) (η : FirstOrderLFP.RelEnv N (P' ∘ Fin.succ)) :
    FirstOrderLFP.Boolean.lfpSet N body η (envEquiv e Γ v) =
      encode (envEquiv e (P' 0).sorts) (FirstOrderLFP.Boolean.lfpSet M body (pullRelations e η) v) := by
  apply lfp_retraction _ (envEquiv e (P' 0).sorts).injective
  intro X
  apply Set.ext
  intro y
  obtain ⟨x, rfl⟩ := (envEquiv e (P' 0).sorts).surjective y
  obtain ⟨θ, hθ, _⟩ := FirstOrderLFP.extends_exists_unique M ht hp x v
  have hθ' := envEquiv_extends e ht hp x v θ hθ
  rw [FirstOrderLFP.Boolean.bodyOperator_iff N ht hp body η (envEquiv e Γ v) X _ _ hθ']
  change _ ↔ (envEquiv e (P' 0).sorts x) ∈ encode (envEquiv e (P' 0).sorts)
    (FirstOrderLFP.Boolean.bodyOperator M body (pullRelations e η) v (restrict (envEquiv e (P' 0).sorts) X))
  have member : (envEquiv e (P' 0).sorts x) ∈ encode (envEquiv e (P' 0).sorts)
      (FirstOrderLFP.Boolean.bodyOperator M body (pullRelations e η) v (restrict (envEquiv e (P' 0).sorts) X)) ↔
      x ∈ FirstOrderLFP.Boolean.bodyOperator M body (pullRelations e η) v (restrict (envEquiv e (P' 0).sorts) X) := by
    exact Iff.of_eq (congrArg (fun Z => x ∈ Z)
      (restrict_encode (envEquiv e (P' 0).sorts) (envEquiv e (P' 0).sorts).injective _))
  rw [member, FirstOrderLFP.Boolean.bodyOperator_iff M ht hp body (pullRelations e η) v _ x θ hθ]
  have h := ih θ (FirstOrderLFP.insertRel N P' η X)
  rw [pullRelations_insert] at h
  exact h.symm
/-- Signed Boolean LFP truth is invariant under actual public structure
isomorphisms, with all predicate environments pulled back on genuine tuples. -/
theorem formula_iso (e : M.toStructure ≅ N.toStructure) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool} (p : FirstOrderLFP.Boolean.Formula S P Γ σ) :
    ∀ (v : FirstOrderLFP.ObjEnv M Γ) (η : FirstOrderLFP.RelEnv N P),
      v ∈ p.denote M (pullRelations e η) ↔ envEquiv e Γ v ∈ p.denote N η := by
  induction p with
  | base p => intro v η; exact GuardedFOL.holds_iso e p v
  | @pred r k P Γ σ i positive args =>
      intro v η
      change envEquiv e (P i).sorts (fun j => (args j).eval M.toStructure.toAlgebra v) ∈ η i ↔
        (fun j => (args j).eval N.toStructure.toAlgebra (envEquiv e _ v)) ∈ η i
      rw [tuple_eval_iso]
  | neg p ih => intro v η; exact not_congr (ih v η)
  | conj p q hp hq => intro v η; exact and_congr (hp v η) (hq v η)
  | disj p q hp hq => intro v η; exact or_congr (hp v η) (hq v η)
  | @all r k P σ Δ p ih =>
      show ∀ (v : FirstOrderLFP.ObjEnv M (Δ ∘ Fin.succ)) (η : FirstOrderLFP.RelEnv N P),
        v ∈ (FirstOrderLFP.Boolean.Formula.all p).denote M (pullRelations e η) ↔
          envEquiv e (Δ ∘ Fin.succ) v ∈ (FirstOrderLFP.Boolean.Formula.all p).denote N η
      intro v η
      change (∀ x : M.toStructure.carrier (Δ 0),
        (show FirstOrderLFP.ObjEnv M Δ from Fin.cases x v) ∈ p.denote M (pullRelations e η)) ↔
        ∀ y : N.toStructure.carrier (Δ 0),
          (show FirstOrderLFP.ObjEnv N Δ from Fin.cases y (envEquiv e _ v)) ∈ p.denote N η
      have hcase (x : M.toStructure.carrier (Δ 0)) :
          (show FirstOrderLFP.ObjEnv M Δ from Fin.cases x v) ∈ p.denote M (pullRelations e η) ↔
            (show FirstOrderLFP.ObjEnv N Δ from Fin.cases (e.hom.map (Δ 0) x) (envEquiv e _ v)) ∈ p.denote N η :=
        (ih (show FirstOrderLFP.ObjEnv M Δ from Fin.cases x v) η).trans
          (Iff.of_eq (congrArg (fun θ => θ ∈ p.denote N η) (envEquiv_cases e Δ v x)))
      constructor
      · intro h y
        obtain ⟨x, rfl⟩ := (GuardedFOL.carrierEquiv e (Δ 0)).surjective y
        exact (hcase x).mp (h x)
      · intro h x
        have hx : (show FirstOrderLFP.ObjEnv N Δ from
            Fin.cases (e.hom.map (Δ 0) x) (envEquiv e _ v)) ∈ p.denote N η := h (e.hom.map (Δ 0) x)
        exact (hcase x).mpr hx
  | @ex r k P σ Δ p ih =>
      show ∀ (v : FirstOrderLFP.ObjEnv M (Δ ∘ Fin.succ)) (η : FirstOrderLFP.RelEnv N P),
        v ∈ (FirstOrderLFP.Boolean.Formula.ex p).denote M (pullRelations e η) ↔
          envEquiv e (Δ ∘ Fin.succ) v ∈ (FirstOrderLFP.Boolean.Formula.ex p).denote N η
      intro v η
      change (∃ x : M.toStructure.carrier (Δ 0),
        (show FirstOrderLFP.ObjEnv M Δ from Fin.cases x v) ∈ p.denote M (pullRelations e η)) ↔
        ∃ y : N.toStructure.carrier (Δ 0),
          (show FirstOrderLFP.ObjEnv N Δ from Fin.cases y (envEquiv e _ v)) ∈ p.denote N η
      have hcase (x : M.toStructure.carrier (Δ 0)) :
          (show FirstOrderLFP.ObjEnv M Δ from Fin.cases x v) ∈ p.denote M (pullRelations e η) ↔
            (show FirstOrderLFP.ObjEnv N Δ from Fin.cases (e.hom.map (Δ 0) x) (envEquiv e _ v)) ∈ p.denote N η :=
        (ih (show FirstOrderLFP.ObjEnv M Δ from Fin.cases x v) η).trans
          (Iff.of_eq (congrArg (fun θ => θ ∈ p.denote N η) (envEquiv_cases e Δ v x)))
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨e.hom.map (Δ 0) x, ?_⟩
        exact (hcase x).mp hx
      · rintro ⟨y, hy⟩
        obtain ⟨x, rfl⟩ := (GuardedFOL.carrierEquiv e (Δ 0)).surjective y
        refine ⟨x, ?_⟩
        exact (hcase x).mpr hy
  | @lfp r k P' Γ σ Δ ht hp body args ih =>
      intro v η
      rw [FirstOrderLFP.Boolean.Formula.denote_lfp, FirstOrderLFP.Boolean.Formula.denote_lfp]
      rw [tuple_eval_iso, iso_lfp e ht hp body ih]
      exact (Iff.of_eq (congrArg (fun Z => (fun j => (args j).eval M.toStructure.toAlgebra v) ∈ Z)
        (restrict_encode (envEquiv e (P' 0).sorts) (envEquiv e (P' 0).sorts).injective _))).symm

end Silmaril.Logic.Matching.GuardedLFP.Boolean
