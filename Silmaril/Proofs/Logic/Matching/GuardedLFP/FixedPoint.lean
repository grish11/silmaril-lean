module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Semantics

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

theorem liftTruth_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → MatchingSort S} (p : Profile S)
    (body : FixedPoint.Pattern (signature S).symbols (setContext P) Γ (.base .truth))
    (v : FixedPoint.ObjEnv (signature S).symbols M.base Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
    (y : M.base.carrier (.tuple p)) :
    y ∈ (FixedPoint.Pattern.app (Operation.liftTruth p) (fun _ => body)).denote M.base v η ↔
      ∃ w, w ∈ body.denote M.base v η := by
  constructor
  · rintro ⟨values, hv, _⟩
    exact ⟨values 0, hv 0⟩
  · rintro ⟨w, hw⟩
    refine ⟨fun _ => w, fun _ => hw, ?_⟩
    rw [M.truthLift]
    trivial

theorem tupleBody_raw (M : Model S) {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FixedPoint.Pattern (signature S).symbols (setContext P') (objContext Δ) (.base .truth))
    (v : FixedPoint.ObjEnv (signature S).symbols M.base (objContext Γ))
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
    (y : M.base.carrier (.tuple (P' 0))) :
    y ∈ (tupleBody ht hp body).denote M.base v η ↔
      ∃ x : ∀ i, M.base.carrier (objSort ((P' 0).sorts i)),
        y ∈ M.base.operation (.pack (P' 0)) x ∧
        ∃ w, w ∈ body.denote M.base
          (FixedPoint.Ren.pull M.base.carrier (blockEnv M.base.carrier v x)
            (blockRen (congrArg (objSort ∘ ·) ht) (congrArg (objSort ∘ ·) hp))) η := by
  unfold tupleBody
  rw [bindPrefix_denote]
  apply exists_congr
  intro x
  change (y ∈ (prefixPack (P' 0)).denote M.base _ η ∧ _) ↔ _
  apply and_congr
  · exact Iff.of_eq (congrArg (fun X => y ∈ X) (prefixPack_denote M (P' 0) v x η))
  · exact (liftTruth_denote M (P' 0) _ _ η y).trans
      (exists_congr fun w => Iff.of_eq (congrArg (fun F => w ∈ F η)
        (FixedPoint.Pattern.denote_renameObjects M.base body _ _)))

/-- The source body's universal assignment clause agrees with native existential
prefix binding because its well-sorted extension exists uniquely. -/
theorem tupleBody_denote (M : Model S) {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Formula S P' Δ)
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M η))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
    (y : M.base.carrier (.tuple (P' 0))) :
    y ∈ (tupleBody ht hp (formula body)).denote M.base (fun i => (v i).val) η ↔
      ∃ x : FirstOrderLFP.Tuple (decode M) (P' 0),
        y = tupleEncode M (P' 0) x ∧
        ∀ θ, FirstOrderLFP.Extends θ x v → θ ∈ body.denote (decode M) (restrictEnv M η) := by
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
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext (P' ∘ Fin.succ)))
    (X : Set (M.base.carrier (.tuple (P' 0)))) :
    restrictEnv M (FixedPoint.insert (signature S).symbols M.base η X) =
      FirstOrderLFP.insertRel (decode M) P' (restrictEnv M η) (restrict (tupleEncode M (P' 0)) X) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem native_lfp (M : Model S) {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Formula S P' Δ)
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M η))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext (P' ∘ Fin.succ))) :
    (FixedPoint.Pattern.mu (tupleBody ht hp (formula body))).denote M.base (fun i => (v i).val) η =
      encode (tupleEncode M (P' 0)) (FirstOrderLFP.lfpSet (decode M) body (restrictEnv M η) v) := by
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

/-- No inactive padding enters a translated μ, even when free raw sets contain it. -/
theorem native_lfp_active (M : Model S) {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Formula S P' Δ)
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M η))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext (P' ∘ Fin.succ))) :
    (FixedPoint.Pattern.mu (tupleBody ht hp (formula body))).denote M.base (fun i => (v i).val) η ⊆
      M.base.operation (.active (P' 0)) (fun i => i.elim0) := by
  rw [native_lfp M ht hp body ih]
  rintro y ⟨x, _, rfl⟩
  exact (pack M (P' 0) x).property

theorem lfp_denote (M : Model S) {r k : Nat} {P' : Fin (r+1) → Profile S}
    {Γ : Fin k → S.S} {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Formula S P' Δ)
    (args : ∀ j, EQ.Term S.toSignature Γ ((P' 0).sorts j))
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv (decode M) Δ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P'))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula body).denote M.base (fun i => (θ i).val) η ↔
        θ ∈ body.denote (decode M) (restrictEnv M η))
    (v : FirstOrderLFP.ObjEnv (decode M) Γ)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext (P' ∘ Fin.succ)))
    (w : M.base.carrier (.base .truth)) :
    w ∈ (formula (.lfp ht hp body args)).denote M.base (fun i => (v i).val) η ↔
      v ∈ (FirstOrderLFP.Formula.lfp ht hp body args).denote (decode M) (restrictEnv M η) := by
  rw [formula, tupleDefined_denote]
  change (∃ x, x ∈ (packTerms args).denote M.base _ η ∩
    (FixedPoint.Pattern.mu (tupleBody ht hp (formula body))).denote M.base _ η) ↔ _
  rw [packTerms_denote, native_lfp M ht hp body ih]
  constructor
  · rintro ⟨z, hz, x, hx, he⟩
    have same : x = fun j => (args j).eval (decode M).toStructure.toAlgebra v :=
      tupleEncode_injective M (P' 0) (he.trans hz)
    change (fun j => (args j).eval (decode M).toStructure.toAlgebra v) ∈
      FirstOrderLFP.lfpSet (decode M) body (restrictEnv M η) v
    exact same ▸ hx
  · intro h
    exact ⟨_, rfl, _, h, rfl⟩

end Silmaril.Logic.Matching.GuardedLFP
