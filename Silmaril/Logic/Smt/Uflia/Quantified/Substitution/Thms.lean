module

public import Silmaril.Logic.Smt.Uflia.Quantified.Substitution.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified
variable {U : Type} {A : Signature U}

set_option backward.isDefEq.respectTransparency false in
theorem eval_subst (M : Model A) {k Γ s} (t : Term A (k := k) Γ s) :
    ∀ {l : Nat} {Δ : Fin l → SortCode U} (σ : Substitution A Γ Δ)
      (values : ∀ i, M.carriers.value (Δ i)),
    eval M values (t.subst σ) = eval M (fun i => eval M values (σ i)) t := by
  classical
  induction t with
  | var i => intro l Δ σ values; rfl
  | app op args ih =>
      intro l Δ σ values
      change M.apply op (fun i => eval M values ((args i).subst σ)) = _
      simp only [ih]
      rfl
  | all sort body ih =>
      intro l Δ σ values
      change decide (∀ x : M.carriers.value sort,
        eval M (Fin.cases x values) (body.subst (σ.lift sort)) = true) =
        decide (∀ x : M.carriers.value sort,
          eval M (Fin.cases x (fun i => eval M values (σ i))) body = true)
      congr 1
      apply propext
      have h (x : M.carriers.value sort) :
          (fun i => eval M (Fin.cases x values) (σ.lift sort i)) =
            Fin.cases x (fun i => eval M values (σ i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact eval_weaken M (σ j) sort values x
      simp only [ih, h]
  | ex sort body ih =>
      intro l Δ σ values
      change decide (∃ x : M.carriers.value sort,
        eval M (Fin.cases x values) (body.subst (σ.lift sort)) = true) =
        decide (∃ x : M.carriers.value sort,
          eval M (Fin.cases x (fun i => eval M values (σ i))) body = true)
      congr 1
      apply propext
      have h (x : M.carriers.value sort) :
          (fun i => eval M (Fin.cases x values) (σ.lift sort i)) =
            Fin.cases x (fun i => eval M values (σ i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · exact eval_weaken M (σ j) sort values x
      simp only [ih, h]

set_option backward.isDefEq.respectTransparency false in
theorem eval_instantiate (M : Model A) {k : Nat} {Γ : Fin k → SortCode U}
    {s sort : SortCode U} (body : Term A (Fin.cases sort Γ) s) (t : Term A Γ sort)
    (values : ∀ i, M.carriers.value (Γ i)) :
    eval M values (body.instantiate t) =
      eval M (@Fin.cases k (fun i => M.carriers.value
        ((@Fin.cases k (fun _ => SortCode U) sort Γ) i)) (eval M values t) values) body := by
  rw [Term.instantiate, eval_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem Formula.all_elim (M : Model A) {k : Nat} {Γ : Fin k → SortCode U}
    {sort : SortCode U} (body : Formula A (Fin.cases sort Γ)) (t : Term A Γ sort)
    (values : ∀ i, M.carriers.value (Γ i))
    (h : Formula.Holds (.all sort body) M values) :
    Formula.Holds (body.instantiate t) M values := by
  unfold Formula.Holds
  rw [eval_instantiate]
  exact (Formula.holds_all sort body M values).mp h (eval M values t)

set_option backward.isDefEq.respectTransparency false in
theorem Formula.ex_intro (M : Model A) {k : Nat} {Γ : Fin k → SortCode U}
    {sort : SortCode U} (body : Formula A (Fin.cases sort Γ)) (t : Term A Γ sort)
    (values : ∀ i, M.carriers.value (Γ i))
    (h : Formula.Holds (body.instantiate t) M values) :
    Formula.Holds (.ex sort body) M values := by
  apply (Formula.holds_ex sort body M values).mpr
  refine ⟨eval M values t, ?_⟩
  unfold Formula.Holds at h ⊢
  rw [eval_instantiate] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem Term.subst_id {k : Nat} {Γ : Fin k → SortCode U} {s : SortCode U}
    (t : Term A Γ s) : t.subst (fun i => .var i) = t := by
  induction t with
  | var i => rfl
  | app op args ih =>
      change Term.app op (fun i => (args i).subst (fun j => .var j)) = _
      congr 1
      funext i
      exact ih i
  | @all k Γ sort body ih =>
      have h : Substitution.lift (fun i : Fin k => (Term.var i : Term A Γ (Γ i))) sort =
          (fun i => (Term.var i : Term A (Fin.cases sort Γ) _)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      change Term.all sort (body.subst _) = _
      rw [h]
      exact congrArg (Term.all sort) ih
  | @ex k Γ sort body ih =>
      have h : Substitution.lift (fun i : Fin k => (Term.var i : Term A Γ (Γ i))) sort =
          (fun i => (Term.var i : Term A (Fin.cases sort Γ) _)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      change Term.ex sort (body.subst _) = _
      rw [h]
      exact congrArg (Term.ex sort) ih

/-- A reusable primitive contradiction; clients need not unfold evaluation. -/
theorem Formula.not_holds_lt_self (M : Model A) {k : Nat} {Γ : Fin k → SortCode U}
    (t : Term A Γ .int) (values : ∀ i, M.carriers.value (Γ i)) :
    ¬ Formula.Holds (.app .lt (Fin.cases t (fun _ => t))) M values := by
  classical
  intro h
  unfold Formula.Holds at h
  conv_lhs at h => unfold eval
  simp [Model.apply, Fin.cases, Fin.induction, Fin.induction.go] at h

theorem Formula.holds_eq_self (M : Model A) {k : Nat} {Γ : Fin k → SortCode U}
    {sort : SortCode U} (t : Term A Γ sort) (values : ∀ i, M.carriers.value (Γ i)) :
    Formula.Holds (.app (.eq sort) (Fin.cases t (fun _ => t))) M values := by
  classical
  unfold Formula.Holds
  conv_lhs => unfold eval
  simp [Model.apply, Fin.cases, Fin.induction, Fin.induction.go]

theorem Formula.holds_subst (M : Model A) {k l : Nat}
    {Γ : Fin k → SortCode U} {Δ : Fin l → SortCode U}
    (p : Formula A Γ) (σ : Substitution A Γ Δ)
    (values : ∀ i, M.carriers.value (Δ i)) :
    Formula.Holds (p.subst σ) M values ↔
      Formula.Holds p M (fun i => eval M values (σ i)) := by
  unfold Formula.Holds
  rw [eval_subst]

theorem eval_closed_subst (M : Model A) {l : Nat} {Δ : Fin l → SortCode U}
    {s : SortCode U} (t : Term A (fun i : Fin 0 => i.elim0) s)
    (values : ∀ i, M.carriers.value (Δ i)) :
    eval M values (t.subst (fun i => i.elim0)) = eval M (fun i => i.elim0) t := by
  rw [eval_subst]
  congr 1
  funext i
  exact i.elim0

end Silmaril.Logic.Smt.Uflia.Quantified
