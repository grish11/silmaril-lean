module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.Defs
public import Silmaril.Logic.Smt.Uflia.SortMaps.Syntax.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Hom
open CategoryTheory
variable {A B C : Signature}

private theorem quantified_eval_heq (M : Model B.symbols) {k : Nat}
    {Γ Δ : Fin k → SortCode B.users} {s t : SortCode B.users}
    (hΓ : Γ = Δ) (hs : s = t)
    (p : Quantified.Term B.symbols Γ s) (q : Quantified.Term B.symbols Δ t)
    (hp : HEq p q) (v : ∀ i, M.carriers.value (Γ i))
    (w : ∀ i, M.carriers.value (Δ i)) (hv : ∀ i, HEq (v i) (w i)) :
    HEq (Quantified.eval M v p) (Quantified.eval M w q) := by
  cases hΓ
  cases hs
  cases eq_of_heq hp
  have same : v = w := funext (fun i => eq_of_heq (hv i))
  cases same
  rfl

private theorem quantifiedBody_heq (f : A ⟶ B) {k : Nat} {Γ : Fin k → SortCode A.users}
    (s : SortCode A.users)
    (p : Quantified.Term B.symbols (f.sorts ∘ Fin.cases s Γ) (f.sorts .bool)) :
    HEq (quantifiedBody f s p) p := cast_heq _ _

private theorem quantifiedTerm_heq (f : A ⟶ B) {k : Nat}
    {Γ Δ : Fin k → SortCode A.users} {s t : SortCode A.users}
    (hΓ : Γ = Δ) (hs : s = t)
    (p : Quantified.Term A.symbols Γ s) (q : Quantified.Term A.symbols Δ t)
    (hp : HEq p q) : HEq (quantifiedTerm f p) (quantifiedTerm f q) := by
  cases hΓ
  cases hs
  cases eq_of_heq hp
  rfl

theorem quantifiedTerm_id {k : Nat} {Γ : Fin k → SortCode A.users} {s : SortCode A.users}
    (p : Quantified.Term A.symbols Γ s) : quantifiedTerm (𝟙 A) p = p := by
  induction p with
  | var i => rfl
  | app op args ih =>
    simp only [quantifiedTerm, operation_id]
    exact congrArg (Quantified.Term.app op) (funext ih)
  | all sort body ih =>
    change Quantified.Term.all sort (quantifiedTerm (𝟙 A) body) = Quantified.Term.all sort body
    exact congrArg (Quantified.Term.all sort) ih
  | ex sort body ih =>
    change Quantified.Term.ex sort (quantifiedTerm (𝟙 A) body) = Quantified.Term.ex sort body
    exact congrArg (Quantified.Term.ex sort) ih

theorem quantifiedTerm_comp (f : A ⟶ B) (g : B ⟶ C) {k : Nat}
    {Γ : Fin k → SortCode A.users} {s : SortCode A.users}
    (p : Quantified.Term A.symbols Γ s) :
    quantifiedTerm (f ≫ g) p = quantifiedTerm g (quantifiedTerm f p) := by
  induction p with
  | var i => rfl
  | app op args ih =>
    simp only [quantifiedTerm, operation_comp]
    exact congrArg (Quantified.Term.app (operation g (operation f op))) (funext ih)
  | @all k Γ sort body ih =>
    have inner := quantifiedTerm_heq g (sorts_cons f sort Γ).symm f.bool.symm
      (quantifiedBody f sort (quantifiedTerm f body)) (quantifiedTerm f body)
      (quantifiedBody_heq f sort _)
    have bodies : quantifiedBody (f ≫ g) sort (quantifiedTerm (f ≫ g) body) =
        quantifiedBody g (f.sorts sort)
          (quantifiedTerm g (quantifiedBody f sort (quantifiedTerm f body))) := by
      apply eq_of_heq
      exact (quantifiedBody_heq (f ≫ g) sort _).trans ((heq_of_eq ih).trans
        (((quantifiedBody_heq g (f.sorts sort) _).trans inner).symm))
    have mapped := quantifiedTerm_heq g rfl f.bool
      (quantifiedTerm f (.all sort body))
      (.all (f.sorts sort) (quantifiedBody f sort (quantifiedTerm f body))) (cast_heq _ _)
    apply eq_of_heq
    exact (cast_heq _ _).trans
      ((heq_of_eq (congrArg (Quantified.Term.all (g.sorts (f.sorts sort))) bodies)).trans
        ((mapped.trans (cast_heq _ _)).symm))
  | @ex k Γ sort body ih =>
    have inner := quantifiedTerm_heq g (sorts_cons f sort Γ).symm f.bool.symm
      (quantifiedBody f sort (quantifiedTerm f body)) (quantifiedTerm f body)
      (quantifiedBody_heq f sort _)
    have bodies : quantifiedBody (f ≫ g) sort (quantifiedTerm (f ≫ g) body) =
        quantifiedBody g (f.sorts sort)
          (quantifiedTerm g (quantifiedBody f sort (quantifiedTerm f body))) := by
      apply eq_of_heq
      exact (quantifiedBody_heq (f ≫ g) sort _).trans ((heq_of_eq ih).trans
        (((quantifiedBody_heq g (f.sorts sort) _).trans inner).symm))
    have mapped := quantifiedTerm_heq g rfl f.bool
      (quantifiedTerm f (.ex sort body))
      (.ex (f.sorts sort) (quantifiedBody f sort (quantifiedTerm f body))) (cast_heq _ _)
    apply eq_of_heq
    exact (cast_heq _ _).trans
      ((heq_of_eq (congrArg (Quantified.Term.ex (g.sorts (f.sorts sort))) bodies)).trans
        ((mapped.trans (cast_heq _ _)).symm))

theorem quantifiedSentence_id (p : Quantified.Sentence A.symbols) :
    quantifiedSentence (𝟙 A) p = p := by
  exact eq_of_heq ((cast_heq _ _).trans (heq_of_eq (quantifiedTerm_id p)))

theorem quantifiedSentence_comp (f : A ⟶ B) (g : B ⟶ C)
    (p : Quantified.Sentence A.symbols) :
    quantifiedSentence (f ≫ g) p = quantifiedSentence g (quantifiedSentence f p) := by
  have inner := quantifiedTerm_heq g (sorts_empty f).symm f.bool.symm
    (quantifiedSentence f p) (quantifiedTerm f p) (cast_heq _ _)
  exact eq_of_heq ((cast_heq _ _).trans ((heq_of_eq (quantifiedTerm_comp f g p)).trans
    (((cast_heq _ _).trans inner).symm)))

/-- Open quantified evaluation commutes with the actual sort-changing reduct. -/
theorem eval_quantifiedTerm (f : A ⟶ B) (M : Model B.symbols) {k : Nat}
    {Γ : Fin k → SortCode A.users} {s : SortCode A.users}
    (t : Quantified.Term A.symbols Γ s)
    (values : ∀ i, (carriers f M).value (Γ i)) :
    value f M s (Quantified.eval (reduct f M) values t) =
      Quantified.eval M (fun i => value f M (Γ i) (values i)) (quantifiedTerm f t) := by
  classical
  induction t with
  | var i => rfl
  | app op args ih =>
    exact (apply_operation f M op
      (fun i => Quantified.eval (reduct f M) values (args i))).trans
        (congrArg (M.apply (operation f op)) (funext (fun i => ih i values)))
  | @all k Γ sort body ih =>
    have same (x : (carriers f M).value sort) :
        Quantified.eval M
          (Fin.cases (value f M sort x) (fun i => value f M (Γ i) (values i)))
          (quantifiedBody f sort (quantifiedTerm f body)) =
        Quantified.eval (reduct f M) (Fin.cases x values) body := by
      apply eq_of_heq
      refine (quantified_eval_heq M (sorts_cons f sort Γ).symm f.bool.symm
        _ _ (quantifiedBody_heq f sort _) _
        (fun i => value f M (Fin.cases sort Γ i) (Fin.cases x values i)) ?_).trans ?_
      · intro i
        cases i using Fin.cases <;> rfl
      · exact (heq_of_eq (ih (Fin.cases x values)).symm).trans (value_heq f M .bool _)
    have truth :
        Quantified.eval (reduct f M) values (.all sort body) =
          Quantified.eval M (fun i => value f M (Γ i) (values i))
            (.all (f.sorts sort) (quantifiedBody f sort (quantifiedTerm f body))) := by
      change decide (∀ x, _) = decide (∀ y, _)
      congr 1
      apply propext
      constructor
      · intro h y
        obtain ⟨x, rfl⟩ := (value f M sort).surjective y
        exact (same x).trans (h x)
      · intro h x
        exact (same x).symm.trans (h (value f M sort x))
    apply eq_of_heq
    refine (value_heq f M .bool _).trans ((heq_of_eq truth).trans ?_)
    symm
    exact quantified_eval_heq M rfl f.bool _ _ (cast_heq _ _) _ _ (fun _ => HEq.rfl)
  | @ex k Γ sort body ih =>
    have same (x : (carriers f M).value sort) :
        Quantified.eval M
          (Fin.cases (value f M sort x) (fun i => value f M (Γ i) (values i)))
          (quantifiedBody f sort (quantifiedTerm f body)) =
        Quantified.eval (reduct f M) (Fin.cases x values) body := by
      apply eq_of_heq
      refine (quantified_eval_heq M (sorts_cons f sort Γ).symm f.bool.symm
        _ _ (quantifiedBody_heq f sort _) _
        (fun i => value f M (Fin.cases sort Γ i) (Fin.cases x values i)) ?_).trans ?_
      · intro i
        cases i using Fin.cases <;> rfl
      · exact (heq_of_eq (ih (Fin.cases x values)).symm).trans (value_heq f M .bool _)
    have truth :
        Quantified.eval (reduct f M) values (.ex sort body) =
          Quantified.eval M (fun i => value f M (Γ i) (values i))
            (.ex (f.sorts sort) (quantifiedBody f sort (quantifiedTerm f body))) := by
      change decide (∃ x, _) = decide (∃ y, _)
      congr 1
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨value f M sort x, (same x).trans hx⟩
      · rintro ⟨y, hy⟩
        obtain ⟨x, rfl⟩ := (value f M sort).surjective y
        exact ⟨x, (same x).symm.trans hy⟩
    apply eq_of_heq
    refine (value_heq f M .bool _).trans ((heq_of_eq truth).trans ?_)
    symm
    exact quantified_eval_heq M rfl f.bool _ _ (cast_heq _ _) _ _ (fun _ => HEq.rfl)

theorem holds_quantifiedSentence (f : A ⟶ B) (M : Model B.symbols)
    (p : Quantified.Sentence A.symbols) :
    (quantifiedSentence f p).Holds M ↔ p.Holds (reduct f M) := by
  have ev := eval_quantifiedTerm f M p (fun i => i.elim0)
  have shifted := quantified_eval_heq M (sorts_empty f).symm f.bool.symm
    (quantifiedSentence f p) (quantifiedTerm f p) (cast_heq _ _)
    (fun i => i.elim0) (fun i => (value f M (Fin.elim0 i)).toFun (i.elim0))
    (fun i => i.elim0)
  have same : Quantified.eval M (fun i => i.elim0) (quantifiedSentence f p) =
      Quantified.eval (reduct f M) (fun i => i.elim0) p := by
    apply eq_of_heq
    exact shifted.trans ((heq_of_eq ev.symm).trans (value_heq f M .bool _))
  exact iff_of_eq (congrArg (fun b : Bool => b = true) same)

end Silmaril.Logic.Smt.Uflia.SortMaps.Hom
