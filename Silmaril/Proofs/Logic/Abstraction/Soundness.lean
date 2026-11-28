module

public import Silmaril.Logic.Abstraction.Soundness.Defs
import Silmaril.Logic.Abstraction.Thms
public import Mathlib.Data.Set.Finite.Basic

namespace Silmaril.Proofs.Logic.Abstraction.Soundness

open Silmaril.Logic.Abstraction

variable {S : Signature}

private theorem fresh_of_instantiate {x k l : Nat} (t : Term S k)
    (σ : Fin k → Term S l) (h : (t.instantiate σ).Fresh x) : t.Fresh x := by
  induction t generalizing l with
  | bound => trivial
  | @free _ n y args ih =>
    cases n with
    | zero => exact h
    | succ n => exact fun i => ih i σ (h i)
  | app a args ih => exact fun i => ih i _ (h i)

private theorem eval_update_of_fresh (A : Algebra S) (ν : Valuation A.Carrier)
    (x : Nat) (u : A.Carrier) {k : Nat} (t : Term S k) (h : t.Fresh x)
    (env : Fin k → A.Carrier) : t.eval A (ν.update x u) env = t.eval A ν env := by
  induction t with
  | bound => rfl
  | @free _ n y args ih =>
    cases n with
    | zero =>
      have different : y ≠ x := Ne.symm h
      simp only [Term.eval, Valuation.update, ite_eq_right different]
      exact congrArg (ν 0 y) (Subsingleton.elim _ _)
    | succ n =>
      exact congrArg (ν (n + 1) y) (funext fun i => ih i (h i) env)
  | app a args ih =>
    exact congrArg (A.op a) (funext fun i => funext fun values =>
      ih i (h i) (Fin.addCases env values))

/-- Perform the named opening's nullary updates one at a time. -/
private def updateMany {U : Type} (ν : Valuation U) :
    {k : Nat} → (Fin k → Nat) → (Fin k → U) → Valuation U
  | 0, _, _ => ν
  | _ + 1, names, values =>
    updateMany (ν.update (names 0) (values 0)) (names ∘ Fin.succ) (values ∘ Fin.succ)

private theorem updateMany_closed {A : Algebra S} (V : ValuationSpace A)
    {ν : Valuation A.Carrier} (hν : ν ∈ V.admissible) {k : Nat}
    (names : Fin k → Nat) (values : Fin k → A.Carrier) :
    updateMany ν names values ∈ V.admissible := by
  induction k generalizing ν with
  | zero => exact hν
  | succ k ih =>
    exact ih (V.update_closed hν (names 0) (values 0)) (names ∘ Fin.succ) (values ∘ Fin.succ)

private theorem updateMany_outside {U : Type} (ν : Valuation U) {k : Nat}
    (names : Fin k → Nat) (values : Fin k → U) (x : Nat) (h : ∀ i, x ≠ names i) :
    updateMany ν names values 0 x = ν 0 x := by
  induction k generalizing ν with
  | zero => rfl
  | succ k ih =>
    rw [updateMany, ih _ (names ∘ Fin.succ) (values ∘ Fin.succ) (fun i => h i.succ)]
    simp only [Valuation.update, ite_eq_right (h 0)]

private theorem updateMany_at {U : Type} (ν : Valuation U) {k : Nat}
    (names : Fin k → Nat) (distinct : Function.Injective names) (values : Fin k → U)
    (i : Fin k) : updateMany ν names values 0 (names i) Fin.elim0 = values i := by
  induction k generalizing ν with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [updateMany, updateMany_outside]
      · simp [Valuation.update]
      · exact fun j h => Fin.succ_ne_zero j (distinct h).symm
    · exact ih _ (names ∘ Fin.succ) (distinct.comp (Fin.succ_injective k))
        (values ∘ Fin.succ) j

private theorem eval_updateMany_of_fresh (A : Algebra S) (ν : Valuation A.Carrier)
    {k l : Nat} (t : Term S l) (names : Fin k → Nat) (values : Fin k → A.Carrier)
    (h : ∀ i, t.Fresh (names i)) (env : Fin l → A.Carrier) :
    t.eval A (updateMany ν names values) env = t.eval A ν env := by
  induction k generalizing ν with
  | zero => rfl
  | succ k ih =>
    rw [updateMany, ih _ (names ∘ Fin.succ) (values ∘ Fin.succ) (fun i => h i.succ)]
    exact eval_update_of_fresh A ν _ _ t (h 0) env

private theorem eval_openWith (A : Algebra S) (ν : Valuation A.Carrier) {k : Nat}
    (p : Template S k) (names : Fin k → Nat) :
    (p.openWith names).eval A ν Fin.elim0 =
      p.eval A ν (fun i => ν 0 (names i) Fin.elim0) := by
  cases k with
  | zero => exact congrArg (p.eval A ν) (Subsingleton.elim _ _)
  | succ k =>
    rw [Term.openWith, Term.eval_instantiate]
    apply congrArg (p.eval A ν)
    funext i
    exact congrArg (ν 0 (names i)) (Subsingleton.elim _ _)

private theorem eval_openWith_updates (A : Algebra S) (ν : Valuation A.Carrier) {k : Nat}
    (p : Template S k) (names : Fin k ↪ Nat) (fresh : ∀ i, p.Fresh (names i))
    (values : Fin k → A.Carrier) :
    (p.openWith names).eval A (updateMany ν names values) Fin.elim0 = p.eval A ν values := by
  rw [eval_openWith, eval_updateMany_of_fresh A ν p names values fresh]
  exact congrArg (p.eval A ν) (funext (updateMany_at ν names names.injective values))

/-- Every evaluation of the old template can be matched by the changed template.
Assign each retained binder its old value, and each added binder its free value in `ν`. -/
private theorem bind_eval (A : Algebra S) (ν : Valuation A.Carrier) {k l : Nat}
    {p : Template S k} {q : Template S l} (oldNames : Fin k ↪ Nat) (newNames : Fin l ↪ Nat)
    (oldFresh : ∀ i, p.Fresh (oldNames i)) (newFresh : ∀ j, q.Fresh (newNames j))
    (sameBody : p.openWith oldNames = q.openWith newNames)
    (removed : ∀ i, oldNames i ∉ Set.range newNames → (p.openWith oldNames).Fresh (oldNames i))
    (values : Fin k → A.Carrier) :
    ∃ newValues : Fin l → A.Carrier, q.eval A ν newValues = p.eval A ν values := by
  have unaffected : ∀ i, q.Fresh (oldNames i) := by
    intro i
    by_cases h : oldNames i ∈ Set.range newNames
    · obtain ⟨j, hj⟩ := h
      exact hj ▸ newFresh j
    · have fresh : (q.openWith newNames).Fresh (oldNames i) := sameBody ▸ removed i h
      cases l with
      | zero => exact fresh
      | succ l => exact fresh_of_instantiate q (fun j => Term.var (newNames j)) fresh
  let μ := updateMany ν oldNames values
  let newValues := fun j : Fin l => μ 0 (newNames j) Fin.elim0
  refine ⟨newValues, ?_⟩
  calc
    q.eval A ν newValues = q.eval A μ newValues :=
      (eval_updateMany_of_fresh A ν q oldNames values unaffected newValues).symm
    _ = (q.openWith newNames).eval A μ Fin.elim0 := (eval_openWith A μ q newNames).symm
    _ = (p.openWith oldNames).eval A μ Fin.elim0 := by rw [sameBody]
    _ = p.eval A ν values := eval_openWith_updates A ν p oldNames oldFresh values

public theorem finite {theory : Set (Rule S)} {Γ : Set (Premise S)} {t : Term S 0}
    (h : Derives theory Γ t) : Γ.Finite := by
  induction h with
  | @«axiom» r _ => exact r.premises.finite_toSet
  | assume t => exact Set.finite_singleton (⟨0, t⟩ : Premise S)
  | add p _ ih => exact ih.insert p
  | bind _ _ _ _ _ _ _ ih => exact (ih.subset (Set.subset_insert _ _)).insert _
  | subst σ _ ih => exact ih.image (Premise.subst σ)
  | varElim _ _ _ _ ih => exact ih.subset (Set.subset_insert _ _)
  | infer _ _ _ _ _ left right => exact (left.subset (Set.subset_insert _ _)).union right

/-- The set-indexed version of `Rule.HoldsAt` agrees definitionally on a rule's antecedent. -/
private def HoldsAt (M : Model S) (ν : Valuation M.algebra.Carrier)
    (Γ : Set (Premise S)) (t : Term S 0) : Prop :=
  letI := M.truth.lattice
  ∀ b : M.truth.Truth, (∀ p ∈ Γ, ∀ args : Fin p.1 → M.algebra.Carrier,
    b ≤ M.truth.classify (p.2.eval M.algebra ν args)) →
    b ≤ M.truth.classify (t.eval M.algebra ν Fin.elim0)

private theorem sound {theory : Set (Rule S)} {Γ : Set (Premise S)} {t : Term S 0}
    (h : Derives theory Γ t) (M : Model S) (hM : ∀ r ∈ theory, M.Sat r) :
    ∀ ν ∈ M.space.admissible, HoldsAt M ν Γ t := by
  let _ := M.truth.lattice
  induction h with
  | «axiom» hr => exact hM _ hr
  | assume t =>
    intro ν hν b lower
    exact lower ⟨0, t⟩ rfl Fin.elim0
  | add p _ ih =>
    intro ν hν b lower
    exact ih ν hν b (fun q hq => lower q (Set.mem_insert_of_mem p hq))
  | @bind Γ t k l p q oldNames newNames oldFresh newFresh sameBody removed _ ih =>
    intro ν hν b lower
    apply ih ν hν b
    intro a ha args
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · obtain ⟨values, heq⟩ :=
        bind_eval M.algebra ν oldNames newNames oldFresh newFresh sameBody removed args
      rw [← heq]
      exact lower ⟨l, q⟩ (Set.mem_insert _ _) values
    · exact lower a (Set.mem_insert_of_mem _ ha) args
  | @subst Γ t σ _ ih =>
    intro ν hν b lower
    rw [Term.eval_subst]
    apply ih _ (M.space.subst_closed hν σ) b
    intro p hp args
    rw [← Term.eval_subst]
    exact lower (p.subst σ) (Set.mem_image_of_mem _ hp) args
  | @varElim Γ t x fresh conclusionFresh _ ih =>
    intro ν hν b lower
    let topValue := M.truth.includeValue ⊤
    rw [← eval_update_of_fresh M.algebra ν x topValue t conclusionFresh]
    apply ih _ (M.space.update_closed hν x topValue) b
    intro p hp args
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · simp [Term.var, Term.eval, Valuation.update, topValue, M.truth.classify_include]
    · rw [eval_update_of_fresh M.algebra ν x topValue p.2 (fresh p hp) args]
      exact lower p hp args
  | @infer Γ Δ t k p names fresh premisesFresh _ _ consumer supplier =>
    intro ν hν b lower
    apply consumer ν hν b
    intro q hq args
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · rw [← eval_openWith_updates M.algebra ν p names fresh args]
      apply supplier _ (updateMany_closed M.space hν names args) b
      intro a ha values
      rw [eval_updateMany_of_fresh M.algebra ν a.2 names args (premisesFresh a ha)]
      exact lower a (Set.mem_union_right _ ha) values
    · exact lower q (Set.mem_union_left _ hq) args

public theorem sat {theory : Set (Rule S)} {r : Rule S}
    (h : r.Derivable theory) (M : Model S) (hM : ∀ a ∈ theory, M.Sat a) : M.Sat r :=
  sound h M hM

end Silmaril.Proofs.Logic.Abstraction.Soundness
