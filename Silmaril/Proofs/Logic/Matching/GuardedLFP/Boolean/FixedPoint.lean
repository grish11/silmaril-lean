module

public import Silmaril.Logic.Matching.GuardedLFP.Boolean.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Boolean
open Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

/-- The source body's universal assignment clause agrees with native existential
prefix binding because its well-sorted extension exists uniquely. -/
theorem tupleBody_denote (M : Model S) {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {σ : Fin r → Bool} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Boolean.Formula S P' Δ (Fin.cases true σ))
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M (Fin.cases true σ) η))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
    (y : M.base.carrier (.tuple (P' 0))) :
    y ∈ (tupleBody ht hp (formula body)).denote M.base (fun i => (v i).val) η ↔
      ∃ x : FirstOrderLFP.Tuple (decode M) (P' 0),
        y = tupleEncode M (P' 0) x ∧
        ∀ θ, FirstOrderLFP.Extends θ x v → θ ∈ body.denote (decode M) (restrictEnv M (Fin.cases true σ) η) := by
  rw [tupleBody_raw]
  constructor
  · show _ → ∃ x : FirstOrderLFP.Tuple (decode M) (P' 0), _
    rintro ⟨raw, hpack, w, hw⟩
    let x : FirstOrderLFP.Tuple (decode M) (P' 0) :=
      fun i => ⟨raw i, (M.pack_strict _ _ _ hpack).1 i⟩
    refine ⟨x, ?_, ?_⟩
    · have hm : y ∈ {(pack M (P' 0) x).val} := pack_graph M (P' 0) x ▸ hpack
      exact hm
    · intro θ hθ
      rw [blockPull_eq M ht hp x v θ hθ] at hw
      exact (ih θ η w).mp hw
  · show (∃ x : FirstOrderLFP.Tuple (decode M) (P' 0), _) → _
    rintro ⟨x, rfl, hx⟩
    obtain ⟨θ, hθ, _⟩ := FirstOrderLFP.extends_exists_unique (decode M) ht hp x v
    refine ⟨fun i => (x i).val, ?_, ?_⟩
    · rw [pack_graph M]
      exact Set.mem_singleton _
    · let w := Classical.choice (M.base.nonempty (.base .truth))
      refine ⟨w, ?_⟩
      rw [blockPull_eq M ht hp x v θ hθ]
      exact (ih θ η w).mpr (hx θ hθ)
theorem restrictEnv_insert (M : Model S) {r : Nat} {P' : Fin (r+1) → Profile S}
    (σ : Fin r → Bool)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext (P' ∘ Fin.succ)))
    (X : Set (M.base.carrier (.tuple (P' 0)))) :
    restrictEnv M (Fin.cases true σ) (FixedPoint.insert (signature S).symbols M.base η X) =
      FirstOrderLFP.insertRel (decode M) P' (restrictEnv M σ η) (restrict (tupleEncode M (P' 0)) X) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem native_lfp (M : Model S) {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {σ : Fin r → Bool} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Boolean.Formula S P' Δ (Fin.cases true σ))
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M (Fin.cases true σ) η))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext (P' ∘ Fin.succ))) :
    (FixedPoint.Pattern.mu (tupleBody ht hp (formula body))).denote M.base (fun i => (v i).val) η =
      encode (tupleEncode M (P' 0)) (FirstOrderLFP.Boolean.lfpSet (decode M) body (restrictEnv M σ η) v) := by
  apply lfp_retraction _ (tupleEncode_injective M (P' 0))
  intro X
  apply Set.ext
  intro y
  change y ∈ (tupleBody ht hp (formula body)).denote M.base _ (FixedPoint.insert _ _ η X) ↔ _
  rw [tupleBody_denote M ht hp body ih, restrictEnv_insert]
  constructor
  · rintro ⟨x, hxy, hx⟩
    exact ⟨x, hx, hxy.symm⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hxy.symm, hx⟩

theorem lfp_denote (M : Model S) {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {σ : Fin r → Bool} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Boolean.Formula S P' Δ (Fin.cases true σ))
    (args : ∀ j, EQ.Term S.toSignature Γ ((P' 0).sorts j))
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M (Fin.cases true σ) η))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext (P' ∘ Fin.succ)))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (formula (.lfp ht hp body args)).denote M.base (fun i => (v i).val) η ↔
      v ∈ (FirstOrderLFP.Boolean.Formula.lfp ht hp body args).denote (decode M) (restrictEnv M σ η) := by
  rw [formula, tupleDefined_denote]
  change (∃ x, x ∈ (packTerms args).denote M.base _ η ∩
    (FixedPoint.Pattern.mu (tupleBody ht hp (formula body))).denote M.base _ η) ↔ _
  rw [packTerms_denote, native_lfp M ht hp body ih]
  constructor
  · rintro ⟨z, hz, x, hx, he⟩
    have same : x = fun j => (args j).eval (decode M).toStructure.toAlgebra v :=
      tupleEncode_injective M (P' 0) (he.trans hz)
    change (fun j => (args j).eval (decode M).toStructure.toAlgebra v) ∈
      FirstOrderLFP.Boolean.lfpSet (decode M) body (restrictEnv M σ η) v
    exact same ▸ hx
  · intro h
    exact ⟨_, rfl, _, h, rfl⟩

end Silmaril.Logic.Matching.GuardedLFP.Boolean
