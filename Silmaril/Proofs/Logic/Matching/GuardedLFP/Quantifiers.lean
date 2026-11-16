module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.FixedPoint

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

theorem denote_context_cast (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ Δ : Fin k → MatchingSort S} {s : MatchingSort S} (h : Γ = Δ)
    (p : FixedPoint.Pattern (signature S).symbols (setContext P) Γ s)
    (v : FixedPoint.ObjEnv (signature S).symbols M.base Δ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P)) :
    (h ▸ p).denote M.base v η = p.denote M.base (h.symm ▸ v) η := by cases h; rfl

theorem quantified_env (M : Model S) {k : Nat} (Δ : Fin (k+1) → S.S)
    (v : ∀ i : Fin k, M.base.carrier (objSort (Δ i.succ))) (x : M.base.carrier (objSort (Δ 0))) :
    ((context_extend Δ).symm ▸ (show (∀ i, M.base.carrier (Fin.cases (objSort (Δ 0))
      (objContext (Δ ∘ Fin.succ)) i)) from Fin.cases x v) : ∀ i, M.base.carrier (objContext Δ i)) =
      (fun i => Fin.cases x v i) := by
  funext i
  cases i using Fin.cases with
  | zero => exact eq_of_heq (GuardedFOL.context_cast_apply M.base.carrier (context_extend Δ).symm
      (show (∀ i, M.base.carrier (Fin.cases (objSort (Δ 0)) (objContext (Δ ∘ Fin.succ)) i)) from Fin.cases x v) 0)
  | succ i => exact eq_of_heq (GuardedFOL.context_cast_apply M.base.carrier (context_extend Δ).symm
      (show (∀ i, M.base.carrier (Fin.cases (objSort (Δ 0)) (objContext (Δ ∘ Fin.succ)) i)) from Fin.cases x v) i.succ)

theorem quantified_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    (Δ : Fin (k+1) → S.S)
    (body : FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Δ) (.base .truth))
    (v : ∀ i : Fin k, M.base.carrier (objSort (Δ i.succ)))
    (x : M.base.carrier (objSort (Δ 0)))
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P)) :
    ((context_extend Δ) ▸ body).denote M.base (Fin.cases x v) η =
      body.denote M.base (fun i => Fin.cases x v i) η :=
  (denote_context_cast M (context_extend Δ) body _ η).trans
    (congrArg (fun ρ => body.denote M.base ρ η) (quantified_env M Δ v x))

theorem raw_cases (M : Model S) {k : Nat} (Δ : Fin (k+1) → S.S)
    (v : FirstOrderLFP.ObjEnv (decode M) (Δ ∘ Fin.succ))
    (x : (decode M).toStructure.carrier (Δ 0)) :
    (fun i => ((show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases x v) i).val) = (fun i => Fin.cases x.val (fun j => (v j).val) i :
      ∀ i, M.base.carrier (objContext Δ i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem mapped_guard_denote (M : Model S) {k : Nat} (Δ : Fin (k+1) → S.S)
    (v : ∀ i, M.base.carrier (objContext Δ i)) (w : M.base.carrier (.base .truth)) :
    w ∈ M.base.denote v ((baseSignature S).pattern (GuardedFOL.activeGuard Δ)) ↔
      v 0 ∈ (baseReduct M.base).operation (.active (Δ 0)) (fun i => i.elim0) := by
  exact Iff.of_eq (congrArg (fun X => w ∈ X)
    (SortMaps.Hom.denote_pattern (baseSignature S) M.base (GuardedFOL.activeGuard Δ) v)) |>.trans
      (GuardedFOL.activeGuard_denote (guardedModel M) v w)

theorem all_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Δ : Fin (k+1) → S.S} (body : FirstOrderLFP.Formula S P Δ)
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M η))
    (v : FirstOrderLFP.ObjEnv (decode M) (Δ ∘ Fin.succ))
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (formula (.all body)).denote M.base (fun i => (v i).val) η ↔
      v ∈ (FirstOrderLFP.Formula.all body).denote (decode M) (restrictEnv M η) := by
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
      (show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases x v) ∈ body.denote (decode M) (restrictEnv M η) at h
    by_cases hx : x ∈ (baseReduct M.base).operation (.active (Δ 0)) (fun i => i.elim0)
    · right
      have hb : w ∈ (formula body).denote M.base
          (fun i => ((show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases ⟨x, hx⟩ v) i).val) η := (ih (show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases ⟨x, hx⟩ v) η w).mpr (h ⟨x, hx⟩)
      exact raw_cases M Δ v ⟨x, hx⟩ ▸ hb
    · exact Or.inl (fun hg => hx ((mapped_guard_denote M Δ _ w).mp hg))
theorem ex_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Δ : Fin (k+1) → S.S} (body : FirstOrderLFP.Formula S P Δ)
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M η))
    (v : FirstOrderLFP.ObjEnv (decode M) (Δ ∘ Fin.succ))
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (formula (.ex body)).denote M.base (fun i => (v i).val) η ↔
      v ∈ (FirstOrderLFP.Formula.ex body).denote (decode M) (restrictEnv M η) := by
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
      body.denote (decode M) (restrictEnv M η) at ha
    refine ⟨a.val, (mapped_guard_denote M Δ _ w).mpr a.property, ?_⟩
    have hb := (ih (show FirstOrderLFP.ObjEnv (decode M) Δ from Fin.cases a v) η w).mpr ha
    exact raw_cases M Δ v a ▸ hb

end Silmaril.Logic.Matching.GuardedLFP
