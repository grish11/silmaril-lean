module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Boolean.FixedPoint

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Boolean
open Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

theorem all_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {σ : Fin r → Bool} {Δ : Fin (k+1) → S.S} (body : FirstOrderLFP.Boolean.Formula S P Δ σ)
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M σ η))
    (v : FirstOrderLFP.ObjEnv (decode M) (Δ ∘ Fin.succ))
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (formula (.all body)).denote M.base (fun i => (v i).val) η ↔
      v ∈ (FirstOrderLFP.Boolean.Formula.all body).denote (decode M) (restrictEnv M σ η) := by
  change (∀ x : M.base.carrier (objSort (Δ 0)),
    w ∈ ((context_extend Δ) ▸ (show FixedPoint.Pattern (signature S).symbols (setContext P)
      (objContext Δ) (.base .truth) from FixedPoint.Pattern.disj
      (.base ((baseSignature S).pattern (.neg (GuardedFOL.activeGuard Δ)))) (formula body))).denote
        M.base (Fin.cases x (fun i => (v i).val)) η) ↔ _
  refine (forall_congr' fun x => Iff.of_eq (congrArg (fun X => w ∈ X)
    (quantified_denote M Δ _ (fun i => (v i).val) x η))).trans ?_
  change (∀ x, w ∉ M.base.denote (fun i => Fin.cases x (fun j => (v j).val) i)
    ((baseSignature S).pattern (GuardedFOL.activeGuard Δ)) ∨
    w ∈ (formula body).denote M.base (fun i => Fin.cases x (fun j => (v j).val) i) η) ↔ _
  constructor
  · show _ → ∀ x : (decode M).toStructure.carrier (Δ 0), _
    intro h x
    have hx : w ∉ M.base.denote (fun i => Fin.cases x.val (fun j => (v j).val) i)
        ((baseSignature S).pattern (GuardedFOL.activeGuard Δ)) ∨
        w ∈ (formula body).denote M.base (fun i => Fin.cases x.val (fun j => (v j).val) i) η := h x.val
    rcases hx with hx | hx
    · exact False.elim (hx ((mapped_guard_denote M Δ _ w).mpr x.property))
    · exact (ih (Fin.cases x v) η w).mp ((raw_cases M Δ v x).symm ▸ hx)
  · show _ → ∀ x : M.base.carrier (objSort (Δ 0)), _
    intro h x
    change ∀ x : (decode M).toStructure.carrier (Δ 0),
      (show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases x v) ∈ body.denote (decode M) (restrictEnv M σ η) at h
    by_cases hx : x ∈ (baseReduct M.base).operation (.active (Δ 0)) (fun i => i.elim0)
    · right
      have hb : w ∈ (formula body).denote M.base
          (fun i => ((show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases ⟨x, hx⟩ v) i).val) η := (ih (show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases ⟨x, hx⟩ v) η w).mpr (h ⟨x, hx⟩)
      exact raw_cases M Δ v ⟨x, hx⟩ ▸ hb
    · exact Or.inl (fun hg => hx ((mapped_guard_denote M Δ _ w).mp hg))
theorem ex_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {σ : Fin r → Bool} {Δ : Fin (k+1) → S.S} (body : FirstOrderLFP.Boolean.Formula S P Δ σ)
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M σ η))
    (v : FirstOrderLFP.ObjEnv (decode M) (Δ ∘ Fin.succ))
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (formula (.ex body)).denote M.base (fun i => (v i).val) η ↔
      v ∈ (FirstOrderLFP.Boolean.Formula.ex body).denote (decode M) (restrictEnv M σ η) := by
  change (∃ x : M.base.carrier (objSort (Δ 0)),
    w ∈ ((context_extend Δ) ▸ (show FixedPoint.Pattern (signature S).symbols (setContext P)
      (objContext Δ) (.base .truth) from FixedPoint.Pattern.conj
      (.base ((baseSignature S).pattern (GuardedFOL.activeGuard Δ))) (formula body))).denote
        M.base (Fin.cases x (fun i => (v i).val)) η) ↔ _
  refine (exists_congr fun x => Iff.of_eq (congrArg (fun X => w ∈ X)
    (quantified_denote M Δ _ (fun i => (v i).val) x η))).trans ?_
  change (∃ x, w ∈ M.base.denote (fun i => Fin.cases x (fun j => (v j).val) i)
    ((baseSignature S).pattern (GuardedFOL.activeGuard Δ)) ∧
    w ∈ (formula body).denote M.base (fun i => Fin.cases x (fun j => (v j).val) i) η) ↔ _
  constructor
  · rintro ⟨x, hx, hb⟩
    let a : (decode M).toStructure.carrier (Δ 0) := ⟨x, (mapped_guard_denote M Δ _ w).mp hx⟩
    refine ⟨a, ?_⟩
    exact (ih (show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases a v) η w).mp
      ((raw_cases M Δ v a).symm ▸ hb)
  · rintro ⟨a, ha⟩
    change (show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases a v) ∈
      body.denote (decode M) (restrictEnv M σ η) at ha
    refine ⟨a.val, (mapped_guard_denote M Δ _ w).mpr a.property, ?_⟩
    have hb := (ih (show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases a v) η w).mpr ha
    exact raw_cases M Δ v a ▸ hb

end Silmaril.Logic.Matching.GuardedLFP.Boolean
