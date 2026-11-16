module

public import Silmaril.Logic.Smt.Uflia.Quantified.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified
open CategoryTheory Silmaril.Inst Silmaril.Logic.Algebraic
variable {U : Type} {A B C : Signature U}

theorem Term.map_id {k Γ s} (t : Term A (k := k) Γ s) : t.map (𝟙 A) = t := by
  induction t with
  | var i => rfl
  | app op args ih =>
      have hop : Operation.map (𝟙 A) op = op := by cases op <;> rfl
      simp only [Term.map, hop]
      congr 1
      funext i
      exact ih i
  | all sort body ih => exact congrArg (Term.all sort) ih
  | ex sort body ih => exact congrArg (Term.ex sort) ih

theorem Term.map_comp (f : A ⟶ B) (g : B ⟶ C) {k Γ s}
    (t : Term A (k := k) Γ s) : t.map (f ≫ g) = (t.map f).map g := by
  induction t with
  | var i => rfl
  | app op args ih =>
      have hop : Operation.map (f ≫ g) op = Operation.map g (Operation.map f op) := by
        cases op <;> rfl
      simp only [Term.map, hop]
      congr 1
      funext i
      exact ih i
  | all sort body ih => exact congrArg (Term.all sort) ih
  | ex sort body ih => exact congrArg (Term.ex sort) ih

theorem eval_map (f : A ⟶ B) (M : Model B) {k Γ s}
    (t : Term A (k := k) Γ s) (values : ∀ i, M.carriers.value (Γ i)) :
    eval M values (t.map f) = eval (M.reduct f) values t := by
  classical
  induction t with
  | var i => rfl
  | app op args ih =>
      change M.apply (Operation.map f op) (fun i => eval M values ((args i).map f)) =
        (M.reduct f).apply op (fun i => eval (M.reduct f) values (args i))
      rw [Model.apply_map]
      congr 1
      funext i
      exact ih i values
  | all sort body ih =>
      change decide (∀ x : M.carriers.value sort, eval M (Fin.cases x values) (body.map f) = true) =
        decide (∀ x : M.carriers.value sort, eval (M.reduct f) (Fin.cases x values) body = true)
      simp only [ih]
      rfl
  | ex sort body ih =>
      change decide (∃ x : M.carriers.value sort, eval M (Fin.cases x values) (body.map f) = true) =
        decide (∃ x : M.carriers.value sort, eval (M.reduct f) (Fin.cases x values) body = true)
      simp only [ih]
      rfl

theorem eval_ofCore (M : Model A) {k Γ s}
    (t : ManySorted.Term A.expanded (k := k) Γ s) (values : ∀ i, M.carriers.value (Γ i)) :
    eval M values (Term.ofCore t) = M.algebra.eval values t := by
  induction t with
  | var i => rfl
  | app op args ih =>
      change M.apply op (fun i => eval M values (Term.ofCore (args i))) =
        M.apply op (fun i => M.algebra.eval values (args i))
      congr 1
      funext i
      exact ih i

theorem ground_holds (p : Uflia.Formula A) (M : Model A) :
    (ground p).Holds M ↔ M.Holds p := by
  unfold Sentence.Holds Formula.Holds ground
  rw [eval_ofCore]
  rfl

theorem Sentence.holds_map (f : A ⟶ B) (p : Sentence A) (M : Model B) :
    Sentence.Holds (p.map f) M ↔ p.Holds (M.reduct f) := by
  unfold Sentence.Holds Formula.Holds
  rw [eval_map]
  rfl

theorem Formula.holds_all {k : Nat} {Γ : Fin k → SortCode U} (sort : SortCode U)
    (body : Formula A (k := k + 1) (Fin.cases sort Γ)) (M : Model A)
    (values : ∀ i, M.carriers.value (Γ i)) :
    Formula.Holds (.all sort body) M values ↔
      ∀ x : M.carriers.value sort, Formula.Holds body M (Fin.cases x values) := by
  classical
  unfold Formula.Holds
  conv_lhs => unfold Quantified.eval
  exact decide_eq_true_iff

theorem Formula.holds_ex {k : Nat} {Γ : Fin k → SortCode U} (sort : SortCode U)
    (body : Formula A (k := k + 1) (Fin.cases sort Γ)) (M : Model A)
    (values : ∀ i, M.carriers.value (Γ i)) :
    Formula.Holds (.ex sort body) M values ↔
      ∃ x : M.carriers.value sort, Formula.Holds body M (Fin.cases x values) := by
  classical
  unfold Formula.Holds
  conv_lhs => unfold Quantified.eval
  exact decide_eq_true_iff

noncomputable def plain (U : Type) : Plain (Signature U) where
  Sen A := Sentence A
  map f p := p.map f
  map_id _ := Term.map_id
  map_comp f g p := Term.map_comp f g p
  Mod A := Model A
  reduct f M := M.reduct f
  reduct_id _ := Model.reduct_id
  reduct_comp := Model.reduct_comp
  Sat M p := p.Holds M
  sat_map f M p := Sentence.holds_map f p M

noncomputable abbrev institution (U : Type) := (plain U).toInst
noncomputable abbrev room (A : Signature U) := (plain U).room A

end Silmaril.Logic.Smt.Uflia.Quantified
