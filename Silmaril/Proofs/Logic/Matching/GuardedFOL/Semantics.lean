module

public import Silmaril.Proofs.Logic.Matching.GuardedFOL.Contexts

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

theorem function_graph (M : Model S) {n inputs output} (op : S.Op n inputs output)
    (args : ∀ i, (decode M).carrier (inputs i)) :
    M.base.operation (.function op) (fun i => (args i).val) = {((decode M).op op args).val} :=
  Classical.choose_spec (M.function op args)

theorem term_denote (M : Model S) {k : Nat} {Γ : Fin k → S.S} {s : S.S}
    (t : EQ.Term S.toSignature Γ s) (v : ∀ i, (decode M).carrier (Γ i)) :
    M.base.denote (fun i => (v i).val) (term t) = {(t.eval (decode M).toAlgebra v).val} := by
  induction t with
  | var => rfl
  | app op args ih =>
      show {result | ∃ values, (∀ i, values i ∈ M.base.denote (fun i => (v i).val) (term (args i))) ∧
        result ∈ M.base.operation (.function op) values} = _
      simp only [ih, Set.mem_singleton_iff]
      apply Set.ext
      intro result
      constructor
      · rintro ⟨values, hv, ho⟩
        have hvalues : values = fun i => ((args i).eval (decode M).toAlgebra v).val := funext hv
        subst values
        exact (function_graph M op _ ▸ ho)
      · intro hr
        refine ⟨_, fun _ => rfl, ?_⟩
        exact (function_graph M op _).symm ▸ hr

theorem defined_denote (M : Model S) {k : Nat} {Γ : Fin k → MatchingSort S} {s : S.S}
    (p : FirstOrder.Pattern (signature S).symbols Γ (.object s))
    (v : ∀ i, M.base.carrier (Γ i)) (w : M.base.carrier .truth) :
    w ∈ M.base.denote v (defined p) ↔ ∃ x, x ∈ M.base.denote v p := by
  constructor
  · rintro ⟨values, hv, _⟩
    exact ⟨values 0, hv 0⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun _ => x, fun _ => hx, ?_⟩
    rw [M.definedness]
    trivial

theorem top_denote (M : Model S) {k : Nat} {Γ : Fin k → MatchingSort S}
    (v : ∀ i, M.base.carrier (Γ i)) (w : M.base.carrier .truth) :
    w ∈ M.base.denote v top := by
  refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
  rw [M.truth]
  trivial

theorem relation_member (M : Model S) {n inputs} (r : S.Rel n inputs)
    (args : ∀ i, M.base.carrier (.object (inputs i))) (w : M.base.carrier .truth) :
    w ∈ M.base.operation (.relation r) args ↔ M.base.operation (.relation r) args = Set.univ := by
  rcases M.relation r args with empty | full
  · rw [empty]
    constructor
    · exact False.elim
    · intro h
      have hw : w ∈ (∅ : Set (M.base.carrier .truth)) := h.symm ▸ Set.mem_univ w
      exact hw.elim
  · rw [full]
    exact ⟨fun _ => rfl, fun _ => Set.mem_univ w⟩
end Silmaril.Logic.Matching.GuardedFOL

@[expose] public section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

private theorem denote_cast (M : Model S) {k : Nat} {Γ Δ : Fin k → MatchingSort S}
    {s : MatchingSort S} (h : Γ = Δ) (p : FirstOrder.Pattern (signature S).symbols Γ s)
    (v : ∀ i, M.base.carrier (Δ i)) :
    M.base.denote v (h ▸ p) = M.base.denote (h.symm ▸ v) p := by cases h; rfl

private theorem matching_extend (M : Model S) {k : Nat} {Γ : Fin k → S.S} {Δ : Fin (k+1) → S.S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, M.base.carrier (.object (Γ i)))
    (x : M.base.carrier (.object (Δ 0))) :
    Eq.rec (motive := fun Θ _ => ∀ i, M.base.carrier (Θ i))
      (Fin.cases x v) (context_extend h).symm =
        extend (fun s => M.base.carrier (.object s)) h v x := by
  funext i
  unfold extend
  cases i using Fin.cases with
  | zero =>
      exact eq_of_heq ((context_cast_apply M.base.carrier (context_extend h).symm
        (show (∀ i, M.base.carrier (Fin.cases (.object (Δ 0)) (objContext Γ) i)) from Fin.cases x v) 0).trans
        (context_cast_apply (fun s => M.base.carrier (.object s)) (context_eq h).symm
          (show (∀ i, M.base.carrier (.object (Fin.cases (Δ 0) Γ i))) from Fin.cases x v) 0).symm)
  | succ i =>
      exact eq_of_heq ((context_cast_apply M.base.carrier (context_extend h).symm
        (show (∀ i, M.base.carrier (Fin.cases (.object (Δ 0)) (objContext Γ) i)) from Fin.cases x v) i.succ).trans
        (context_cast_apply (fun s => M.base.carrier (.object s)) (context_eq h).symm
          (show (∀ i, M.base.carrier (.object (Fin.cases (Δ 0) Γ i))) from Fin.cases x v) i.succ).symm)

theorem allContext_denote (M : Model S) {k : Nat} {Γ : Fin k → S.S} {Δ : Fin (k+1) → S.S}
    (h : Δ ∘ Fin.succ = Γ) (p : FirstOrder.Pattern (signature S).symbols (objContext Δ) .truth)
    (v : ∀ i, M.base.carrier (.object (Γ i))) (w : M.base.carrier .truth) :
    w ∈ M.base.denote v (allContext h p) ↔
      ∀ x, w ∈ M.base.denote (extend (fun s => M.base.carrier (.object s)) h v x) p := by
  classical
  change (¬ ∃ x, ¬ w ∈ M.base.denote (Fin.cases x v) ((context_extend h) ▸ p)) ↔ _
  simp only [not_exists, not_not, denote_cast M]
  apply forall_congr'
  intro x
  exact iff_of_eq (congrArg (fun env => w ∈ M.base.denote env p) (matching_extend M h v x))

theorem active_denote (M : Model S) {k : Nat} {Γ : Fin k → MatchingSort S}
    (s : S.S) (v : ∀ i, M.base.carrier (Γ i)) (x : M.base.carrier (.object s)) :
    x ∈ M.base.denote v (.app (.active s) (fun i => i.elim0)) ↔
      x ∈ M.base.operation (.active s) (fun i => i.elim0) := by
  constructor
  · rintro ⟨args, _, ho⟩
    have same : args = (fun i => i.elim0) := funext (fun i => i.elim0)
    exact same ▸ ho
  · intro ho
    exact ⟨fun i => i.elim0, fun i => i.elim0, ho⟩

theorem activeGuard_denote (M : Model S) {k : Nat} {Δ : Fin (k+1) → S.S}
    (v : ∀ i, M.base.carrier (.object (Δ i))) (w : M.base.carrier .truth) :
    w ∈ M.base.denote v (defined (.conj (.var 0) (.app (.active (Δ 0)) (fun i => i.elim0)))) ↔
      v 0 ∈ M.base.operation (.active (Δ 0)) (fun i => i.elim0) := by
  rw [defined_denote]
  constructor
  · rintro ⟨x, hx, ha⟩
    exact hx ▸ (active_denote M _ v x).mp ha
  · intro ha
    exact ⟨v 0, rfl, (active_denote M _ v _).mpr ha⟩

theorem imp_denote (M : Model S) {k : Nat} {Γ : Fin k → MatchingSort S}
    (p q : FirstOrder.Pattern (signature S).symbols Γ .truth)
    (v : ∀ i, M.base.carrier (Γ i)) (w : M.base.carrier .truth) :
    w ∈ M.base.denote v (imp p q) ↔ (w ∈ M.base.denote v p → w ∈ M.base.denote v q) := by
  classical
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨hp, hq⟩
  · intro h ⟨hp, hq⟩
    exact hq (h hp)

/-- Universal native denotation for every admitted raw model, active valuation,
and truth-sort element, including empty source sorts. -/
theorem formula_denote (M : Model S) {k : Nat} {Γ : Fin k → S.S} (p : FOL.Formula S Γ) :
    ∀ (v : ∀ i, (decode M).carrier (Γ i)) (w : M.base.carrier .truth),
      w ∈ M.base.denote (fun i => (v i).val) (formula p) ↔ p.Holds (decode M) v := by
  induction p with
  | @eq k Γ s t u =>
      show ∀ (v : ∀ i, (decode M).carrier (Γ i)) (w : M.base.carrier .truth),
        w ∈ M.base.denote (fun i => (v i).val) (formula (.eq t u)) ↔
          t.eval (decode M).toAlgebra v = u.eval (decode M).toAlgebra v
      intro v w
      rw [formula, defined_denote M]
      simp only [FirstOrder.Model.denote, term_denote M, Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, ht, hu⟩
        exact Subtype.ext (ht.symm.trans hu)
      · intro h
        exact ⟨_, rfl, congrArg Subtype.val h⟩
  | @rel k Γ n inputs r args =>
      show ∀ (v : ∀ i, (decode M).carrier (Γ i)) (w : M.base.carrier .truth),
        w ∈ M.base.denote (fun i => (v i).val) (formula (.rel r args)) ↔
          (decode M).rel r (fun i => (args i).eval (decode M).toAlgebra v)
      intro v w
      change (∃ values, (∀ i, values i ∈ M.base.denote (fun i => (v i).val) (term (args i))) ∧
        w ∈ M.base.operation (.relation r) values) ↔ _
      simp only [term_denote M, Set.mem_singleton_iff]
      constructor
      · rintro ⟨values, hv, ho⟩
        have same : values = fun i => ((args i).eval (decode M).toAlgebra v).val := funext hv
        subst values
        exact (relation_member M r _ w).mp ho
      · intro h
        exact ⟨_, fun _ => rfl, (relation_member M r _ w).mpr h⟩
  | tt => intro v w; exact ⟨fun _ => trivial, fun _ => top_denote M _ w⟩
  | not p ih => intro v w; exact not_congr (ih v w)
  | and p q hp hq => intro v w; exact and_congr (hp v w) (hq v w)
  | @all k Γ Δ h p ih =>
      show ∀ (v : ∀ i, (decode M).carrier (Γ i)) (w : M.base.carrier .truth),
        w ∈ M.base.denote (fun i => (v i).val) (formula (.all h p)) ↔
          ∀ θ, (∀ i, HEq (θ i.succ) (v i)) → p.Holds (decode M) θ
      intro v w
      rw [formula, allContext_denote M]
      simp only [imp_denote M, activeGuard_denote M, extend_zero]
      change (∀ a, a ∈ M.base.operation (.active (Δ 0)) (fun i => i.elim0) →
        w ∈ M.base.denote (extend (fun s => M.base.carrier (.object s)) h (fun i => (v i).val) a) (formula p)) ↔ _
      change _ ↔ ∀ θ, (∀ i, HEq (θ i.succ) (v i)) → p.Holds (decode M) θ
      rw [← forall_extensions (decode M).carrier h v]
      constructor
      · intro hall x
        have hx : w ∈ M.base.denote
            (extend (fun s => M.base.carrier (.object s)) h (fun i => (v i).val) x.val) (formula p) :=
          hall x.val x.property
        rw [← extend_natural (fun _ a => a.val) h v x] at hx
        exact (ih _ w).mp hx
      · intro hall a ha
        let x : (decode M).carrier (Δ 0) := ⟨a, ha⟩
        have hx : w ∈ M.base.denote (fun i => (extend (decode M).carrier h v x i).val) (formula p) :=
          (ih _ w).mpr (hall x)
        rw [extend_natural (fun _ a => a.val) h v x] at hx
        exact hx
end Silmaril.Logic.Matching.GuardedFOL
