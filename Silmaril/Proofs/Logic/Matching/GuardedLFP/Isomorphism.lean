module

public import Silmaril.Logic.Matching.GuardedLFP.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature} {M N : FirstOrderLFP.Model S}

def envEquiv (e : M.toStructure ≅ N.toStructure) {k : Nat} (Γ : Fin k → S.S) :
    FirstOrderLFP.ObjEnv M Γ ≃ FirstOrderLFP.ObjEnv N Γ where
  toFun v i := e.hom.map (Γ i) (v i)
  invFun v i := e.inv.map (Γ i) (v i)
  left_inv v := funext fun i => (GuardedFOL.carrierEquiv e (Γ i)).left_inv (v i)
  right_inv v := funext fun i => (GuardedFOL.carrierEquiv e (Γ i)).right_inv (v i)

def pullRelations (e : M.toStructure ≅ N.toStructure) {r : Nat} {P : Fin r → Profile S}
    (η : FirstOrderLFP.RelEnv N P) : FirstOrderLFP.RelEnv M P :=
  fun i => (envEquiv e (P i).sorts) ⁻¹' η i

theorem pullRelations_insert (e : M.toStructure ≅ N.toStructure)
    {r : Nat} {P' : Fin (r+1) → Profile S}
    (η : FirstOrderLFP.RelEnv N (P' ∘ Fin.succ)) (X : Set (FirstOrderLFP.Tuple N (P' 0))) :
    pullRelations e (FirstOrderLFP.insertRel N P' η X) =
      FirstOrderLFP.insertRel M P' (pullRelations e η) (restrict (envEquiv e (P' 0).sorts) X) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem envEquiv_cases (e : M.toStructure ≅ N.toStructure) {k : Nat}
    (Δ : Fin (k+1) → S.S) (v : FirstOrderLFP.ObjEnv M (Δ ∘ Fin.succ))
    (x : M.toStructure.carrier (Δ 0)) :
    envEquiv e Δ (Fin.cases x v) = Fin.cases (e.hom.map (Δ 0) x) (envEquiv e (Δ ∘ Fin.succ) v) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem map_value_heq (e : M.toStructure ≅ N.toStructure) {a b : S.S} (hs : a = b)
    (x : M.toStructure.carrier a) (y : M.toStructure.carrier b) (h : HEq x y) :
    HEq (e.hom.map a x) (e.hom.map b y) := by
  cases hs
  exact heq_of_eq (congrArg (e.hom.map a) (eq_of_heq h))

theorem envEquiv_extends (e : M.toStructure ≅ N.toStructure) {n k : Nat}
    {w : Fin n → S.S} {Γ : Fin k → S.S} {Δ : Fin (n+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = w) (hp : Δ ∘ Fin.natAdd n = Γ)
    (x : FirstOrderLFP.ObjEnv M w) (v : FirstOrderLFP.ObjEnv M Γ)
    (θ : FirstOrderLFP.ObjEnv M Δ) (hθ : FirstOrderLFP.Extends θ x v) :
    FirstOrderLFP.Extends (envEquiv e Δ θ) (envEquiv e w x) (envEquiv e Γ v) :=
  ⟨fun i => map_value_heq e (congrFun ht i) _ _ (hθ.1 i),
    fun i => map_value_heq e (congrFun hp i) _ _ (hθ.2 i)⟩

theorem iso_lfp (e : M.toStructure ≅ N.toStructure) {r k : Nat}
    {P' : Fin (r+1) → Profile S} {Γ : Fin k → S.S}
    {Δ : Fin ((P' 0).arity+k) → S.S}
    (ht : Δ ∘ Fin.castAdd k = (P' 0).sorts)
    (hp : Δ ∘ Fin.natAdd (P' 0).arity = Γ)
    (body : FirstOrderLFP.Formula S P' Δ)
    (ih : ∀ (θ : FirstOrderLFP.ObjEnv M Δ) (η : FirstOrderLFP.RelEnv N P'),
      θ ∈ body.denote M (pullRelations e η) ↔ envEquiv e Δ θ ∈ body.denote N η)
    (v : FirstOrderLFP.ObjEnv M Γ) (η : FirstOrderLFP.RelEnv N (P' ∘ Fin.succ)) :
    FirstOrderLFP.lfpSet N body η (envEquiv e Γ v) =
      encode (envEquiv e (P' 0).sorts) (FirstOrderLFP.lfpSet M body (pullRelations e η) v) := by
  apply lfp_retraction _ (envEquiv e (P' 0).sorts).injective
  intro X
  apply Set.ext
  intro y
  obtain ⟨x, rfl⟩ := (envEquiv e (P' 0).sorts).surjective y
  obtain ⟨θ, hθ, _⟩ := FirstOrderLFP.extends_exists_unique M ht hp x v
  have hθ' := envEquiv_extends e ht hp x v θ hθ
  rw [FirstOrderLFP.bodyOperator_iff N ht hp body η (envEquiv e Γ v) X _ _ hθ']
  change _ ↔ (envEquiv e (P' 0).sorts x) ∈ encode (envEquiv e (P' 0).sorts)
    (FirstOrderLFP.bodyOperator M body (pullRelations e η) v (restrict (envEquiv e (P' 0).sorts) X))
  have member : (envEquiv e (P' 0).sorts x) ∈ encode (envEquiv e (P' 0).sorts)
      (FirstOrderLFP.bodyOperator M body (pullRelations e η) v (restrict (envEquiv e (P' 0).sorts) X)) ↔
      x ∈ FirstOrderLFP.bodyOperator M body (pullRelations e η) v (restrict (envEquiv e (P' 0).sorts) X) := by
    exact Iff.of_eq (congrArg (fun Z => x ∈ Z)
      (restrict_encode (envEquiv e (P' 0).sorts) (envEquiv e (P' 0).sorts).injective _))
  rw [member, FirstOrderLFP.bodyOperator_iff M ht hp body (pullRelations e η) v _ x θ hθ]
  have h := ih θ (FirstOrderLFP.insertRel N P' η X)
  rw [pullRelations_insert] at h
  exact h.symm
theorem tuple_eval_iso (e : M.toStructure ≅ N.toStructure) {k : Nat}
    {Γ : Fin k → S.S} {p : Profile S}
    (args : ∀ j, EQ.Term S.toSignature Γ (p.sorts j)) (v : FirstOrderLFP.ObjEnv M Γ) :
    (fun j => (args j).eval N.toStructure.toAlgebra (envEquiv e Γ v)) =
      envEquiv e p.sorts (fun j => (args j).eval M.toStructure.toAlgebra v) :=
  funext fun j => (GuardedFOL.eval_hom e.hom (args j) v).symm

/-- Full source-positive LFP truth is invariant under actual public structure
isomorphisms, with all predicate environments pulled back on genuine tuples. -/
theorem formula_iso (e : M.toStructure ≅ N.toStructure) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : FirstOrderLFP.Formula S P Γ) :
    ∀ (v : FirstOrderLFP.ObjEnv M Γ) (η : FirstOrderLFP.RelEnv N P),
      v ∈ p.denote M (pullRelations e η) ↔ envEquiv e Γ v ∈ p.denote N η := by
  induction p with
  | base p => intro v η; exact GuardedFOL.holds_iso e p v
  | @pred r k P Γ i args =>
      intro v η
      change envEquiv e (P i).sorts (fun j => (args j).eval M.toStructure.toAlgebra v) ∈ η i ↔
        (fun j => (args j).eval N.toStructure.toAlgebra (envEquiv e _ v)) ∈ η i
      rw [tuple_eval_iso]
  | conj p q hp hq => intro v η; exact and_congr (hp v η) (hq v η)
  | disj p q hp hq => intro v η; exact or_congr (hp v η) (hq v η)
  | @all r k P Δ p ih =>
      show ∀ (v : FirstOrderLFP.ObjEnv M (Δ ∘ Fin.succ)) (η : FirstOrderLFP.RelEnv N P),
        v ∈ (FirstOrderLFP.Formula.all p).denote M (pullRelations e η) ↔
          envEquiv e (Δ ∘ Fin.succ) v ∈ (FirstOrderLFP.Formula.all p).denote N η
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
  | @ex r k P Δ p ih =>
      show ∀ (v : FirstOrderLFP.ObjEnv M (Δ ∘ Fin.succ)) (η : FirstOrderLFP.RelEnv N P),
        v ∈ (FirstOrderLFP.Formula.ex p).denote M (pullRelations e η) ↔
          envEquiv e (Δ ∘ Fin.succ) v ∈ (FirstOrderLFP.Formula.ex p).denote N η
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
  | @lfp r k P' Γ Δ ht hp body args ih =>
      intro v η
      rw [FirstOrderLFP.Formula.denote_lfp, FirstOrderLFP.Formula.denote_lfp]
      rw [tuple_eval_iso, iso_lfp e ht hp body ih]
      exact (Iff.of_eq (congrArg (fun Z => (fun j => (args j).eval M.toStructure.toAlgebra v) ∈ Z)
        (restrict_encode (envEquiv e (P' 0).sorts) (envEquiv e (P' 0).sorts).injective _))).symm

end Silmaril.Logic.Matching.GuardedLFP
