module

public import Silmaril.Logic.FirstOrder.Variables.Defs

@[expose] public section
namespace Silmaril.Logic.FirstOrder.Variables
open Silmaril.Logic.Institution.Examples
variable {Sg : FOL.Signature} (M : FOL.Structure Sg)

private theorem eval_sort_cast {k : Nat} {Γ : Fin k → Sg.S} {s t : Sg.S}
    (h : s = t) (p : EQ.Term Sg.toSignature Γ s)
    (a : (i : Fin k) → M.carrier (Γ i)) :
    EQ.Term.eval M.toAlgebra a (h ▸ p) =
      cast (congrArg M.carrier h) (EQ.Term.eval M.toAlgebra a p) := by
  cases h
  rfl

/-- Term lookup commutes with type-preserving renaming. -/
theorem eval_rename {k : Nat} {Γ : Fin k → Sg.S} {s : Sg.S}
    (t : EQ.Term Sg.toSignature Γ s) :
    ∀ {l : Nat} {Δ : Fin l → Sg.S} (f : Fin k → Fin l)
      (h : ∀ i, Δ (f i) = Γ i) (a : (i : Fin l) → M.carrier (Δ i)),
      EQ.Term.eval M.toAlgebra a (termRename f h t) =
        EQ.Term.eval M.toAlgebra (pullback M f h a) t := by
  induction t with
  | var i =>
    intro l Δ f h a
    exact eval_sort_cast M (h i) (.var (f i)) a
  | app op args ih =>
    intro l Δ f h a
    simp only [termRename, EQ.Term.eval, ih]

/-- Actual universal semantics normalize to one value plus the old assignment. -/
theorem all_holds {k : Nat} {Γ : Fin k → Sg.S} {Ξ : Fin (k + 1) → Sg.S}
    (tail : Ξ ∘ Fin.succ = Γ) (body : FOL.Formula Sg Ξ)
    (a : (i : Fin k) → M.carrier (Γ i)) :
    FOL.Formula.Holds M (.all tail body) a ↔
      ∀ x : M.carrier (Ξ 0),
        FOL.Formula.Holds M body (extendAssignment M tail x a) := by
  constructor
  · intro h x
    apply h (extendAssignment M tail x a)
    intro i
    exact cast_heq _ _
  · intro h b agree
    have same : b = extendAssignment M tail (b 0) a := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · apply eq_of_heq
        exact (agree j).trans (cast_heq _ _).symm
    rw [same]
    exact h (b 0)

theorem extendAssignment_cons {k : Nat} (s : Sg.S) (Γ : Fin k → Sg.S)
    (x : M.carrier s) (a : (i : Fin k) → M.carrier (Γ i)) :
    extendAssignment M (consTail s Γ) x a = Fin.cases x a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Canonical context extension exposes the bound value at its original sort. -/
theorem all_holds_cons {k : Nat} (s : Sg.S) (Γ : Fin k → Sg.S)
    (body : FOL.Formula Sg (Fin.cases s Γ))
    (a : (i : Fin k) → M.carrier (Γ i)) :
    FOL.Formula.Holds M (.all (Γ := Γ) (consTail s Γ) body) a ↔
      ∀ x : M.carrier s, FOL.Formula.Holds M body (Fin.cases x a) := by
  constructor
  · intro h x
    exact h (Fin.cases x a) (fun _ => HEq.rfl)
  · intro h b agree
    have same : b = Fin.cases (b 0) a := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact eq_of_heq (agree j)
    rw [same]
    exact h (b 0)

private theorem pullback_lift {k l : Nat} {Γ : Fin k → Sg.S} {Δ : Fin l → Sg.S}
    {Ξ : Fin (k + 1) → Sg.S} (tail : Ξ ∘ Fin.succ = Γ)
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i)
    (a : (i : Fin l) → M.carrier (Δ i)) (x : M.carrier (Ξ 0)) :
    pullback M (liftIndex f) (liftSort tail f h) (Fin.cases x a) =
      extendAssignment M tail x (pullback M f h a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · apply eq_of_heq
    exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)).symm

/-- Formula renaming changes only assignment lookup, through actual binders. -/
theorem holds_rename {k : Nat} {Γ : Fin k → Sg.S} (p : FOL.Formula Sg Γ) :
    ∀ {l : Nat} {Δ : Fin l → Sg.S} (f : Fin k → Fin l)
      (h : ∀ i, Δ (f i) = Γ i) (a : (i : Fin l) → M.carrier (Δ i)),
      FOL.Formula.Holds M (rename f h p) a ↔
        FOL.Formula.Holds M p (pullback M f h a) := by
  induction p with
  | eq t u =>
    intro l Δ f h a
    simp only [rename, FOL.Formula.Holds, eval_rename]
  | rel r args =>
    intro l Δ f h a
    simp only [rename, FOL.Formula.Holds, eval_rename]
  | tt => intro l Δ f h a; rfl
  | not p ih =>
    intro l Δ f h a
    exact not_congr (ih f h a)
  | and p q ihp ihq =>
    intro l Δ f h a
    exact and_congr (ihp f h a) (ihq f h a)
  | @all n Γ₀ Ξ tail body ih =>
    intro l Δ f h a
    simp only [rename]
    rw [all_holds_cons M (Ξ 0) Δ, all_holds M tail]
    simp only [ih]
    apply forall_congr'
    intro x
    rw [pullback_lift M tail f h a x]

/-- Syntactic term support controls all semantic variable dependence. -/
theorem eval_eq_of_agree {k : Nat} {Γ : Fin k → Sg.S} {s : Sg.S}
    (t : EQ.Term Sg.toSignature Γ s) :
    ∀ (a b : (i : Fin k) → M.carrier (Γ i)),
      (∀ i, i ∈ termFree t → a i = b i) →
      EQ.Term.eval M.toAlgebra a t = EQ.Term.eval M.toAlgebra b t := by
  induction t with
  | var i =>
    intro a b agree
    exact agree i (by simp [termFree])
  | app op args ih =>
    intro a b agree
    apply congrArg (M.op op)
    funext j
    apply ih j a b
    intro i hi
    apply agree i
    simp only [termFree, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨j, hi⟩

/-- Actual FOL free support gives assignment independence, including quantifiers. -/
theorem holds_iff_of_agree {k : Nat} {Γ : Fin k → Sg.S} (p : FOL.Formula Sg Γ) :
    ∀ (a b : (i : Fin k) → M.carrier (Γ i)),
      (∀ i, i ∈ free p → a i = b i) →
      (FOL.Formula.Holds M p a ↔ FOL.Formula.Holds M p b) := by
  induction p with
  | eq t u =>
    intro a b agree
    have ht := eval_eq_of_agree M t a b (fun i hi => agree i (Finset.mem_union_left _ hi))
    have hu := eval_eq_of_agree M u a b (fun i hi => agree i (Finset.mem_union_right _ hi))
    simp only [FOL.Formula.Holds, ht, hu]
  | rel r args =>
    intro a b agree
    have same : (fun j => EQ.Term.eval M.toAlgebra a (args j)) =
        (fun j => EQ.Term.eval M.toAlgebra b (args j)) := by
      funext j
      apply eval_eq_of_agree M (args j) a b
      intro i hi
      apply agree i
      simp only [free, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨j, hi⟩
    exact Iff.of_eq (congrArg (M.rel r) same)
  | tt => intro a b agree; rfl
  | not p ih =>
    intro a b agree
    exact not_congr (ih a b agree)
  | and p q ihp ihq =>
    intro a b agree
    exact and_congr
      (ihp a b (fun i hi => agree i (Finset.mem_union_left _ hi)))
      (ihq a b (fun i hi => agree i (Finset.mem_union_right _ hi)))
  | all tail body ih =>
    intro a b agree
    rw [all_holds, all_holds]
    apply forall_congr'
    intro x
    apply ih
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      rfl
    · intro hi
      have same := agree j (by simp [free, hi])
      exact congrArg (fun v => cast (congrArg M.carrier (congrFun tail j).symm) v) same

/-- Actual existential syntax ranges over exactly one sorted value. -/
theorem exists_holds {k : Nat} {Γ : Fin k → Sg.S} (s : Sg.S)
    (body : FOL.Formula Sg (Fin.cases s Γ)) (a : (i : Fin k) → M.carrier (Γ i)) :
    FOL.Formula.Holds M (existsFormula s body) a ↔
      ∃ x : M.carrier s, FOL.Formula.Holds M body (Fin.cases x a) := by
  classical
  change (¬ FOL.Formula.Holds M (.all (Γ := Γ) (consTail s Γ) (.not body)) a) ↔ _
  rw [all_holds_cons M s Γ]
  simp only [FOL.Formula.Holds, not_forall, not_not]

private theorem pullback_swap {k : Nat} (cfg bound : Sg.S) (Γ : Fin k → Sg.S)
    (w : M.carrier cfg) (x : M.carrier bound) (a : (i : Fin k) → M.carrier (Γ i)) :
    pullback M swapHead (swapSort cfg bound Γ) (Fin.cases x (Fin.cases w a)) =
      Fin.cases w (Fin.cases x a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl

/-- Binding a capture preserves the exact original current configuration. -/
theorem existsCaptured_holds {k : Nat} (cfg bound : Sg.S) (Γ : Fin k → Sg.S)
    (p : FOL.Formula Sg (Fin.cases cfg (Fin.cases bound Γ)))
    (w : M.carrier cfg) (a : (i : Fin k) → M.carrier (Γ i)) :
    FOL.Formula.Holds M (existsCaptured cfg bound Γ p) (Fin.cases w a) ↔
      ∃ x : M.carrier bound, FOL.Formula.Holds M p
        (consAssignment M cfg (Fin.cases bound Γ) w (consAssignment M bound Γ x a)) := by
  unfold existsCaptured
  rw [exists_holds]
  apply exists_congr
  intro x
  rw [holds_rename]
  exact Iff.of_eq (congrArg (FOL.Formula.Holds M p) (pullback_swap M cfg bound Γ w x a))

/-- Quantifying a whole finite sorted capture block retains configuration slot0
and is exactly rebinding that block, independently of the outer assignment. -/
theorem existsBlock_holds {k : Nat} (cfg : Sg.S) (Γ : Fin k → Sg.S)
    (xs : List Sg.S) :
    ∀ (p : FOL.Formula Sg (Fin.cases cfg (blockContext Γ xs)))
      (w : M.carrier cfg) (a : (i : Fin k) → M.carrier (Γ i)),
      FOL.Formula.Holds M (existsBlock cfg Γ xs p) (Fin.cases w a) ↔
        ∃ b : BlockAssignment M xs,
          FOL.Formula.Holds M p (Fin.cases w (joinAssignment M a xs b)) := by
  induction xs with
  | nil =>
    intro p w a
    exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
  | cons s xs ih =>
    intro p w a
    change FOL.Formula.Holds M
      (existsBlock cfg Γ xs (existsCaptured cfg s (blockContext Γ xs) p))
      (Fin.cases w a) ↔ _
    rw [ih]
    have normalize : ∀ b : BlockAssignment M xs,
        FOL.Formula.Holds M (existsCaptured cfg s (blockContext Γ xs) p)
          (Fin.cases w (joinAssignment M a xs b)) ↔
        ∃ x : M.carrier s, FOL.Formula.Holds M p
          (consAssignment M cfg (Fin.cases s (blockContext Γ xs)) w
            (consAssignment M s (blockContext Γ xs) x (joinAssignment M a xs b))) :=
      fun b => existsCaptured_holds M cfg s (blockContext Γ xs) p w (joinAssignment M a xs b)
    simp only [normalize]
    constructor
    · rintro ⟨b, x, h⟩
      exact ⟨(x, b), h⟩
    · rintro ⟨⟨x, b⟩, h⟩
      exact ⟨b, x, h⟩

end Silmaril.Logic.FirstOrder.Variables
