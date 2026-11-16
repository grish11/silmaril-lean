module

public import Silmaril.Logic.Matching.FirstOrder.Variables.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder

variable {S : Type} {A : Algebraic.ManySorted.Signature S}
variable (M : Model A)

private theorem dependent_congr {α : Type} {β : α → Type}
    (f : (x : α) → β x) {x y : α} (h : x = y) : HEq (f x) (f y) := by
  cases h
  rfl

private theorem mem_denote_sort_cast {k : Nat} {Γ : Fin k → S} {s t : S}
    (h : s = t) (p : Pattern A Γ s) (a : (i : Fin k) → M.carrier (Γ i))
    (w : M.carrier t) : w ∈ M.denote a (h ▸ p) ↔
      cast (congrArg M.carrier h.symm) w ∈ M.denote a p := by
  cases h
  rfl

private theorem cast_eq_iff {s t : S} (h : s = t)
    (x : M.carrier t) (y : M.carrier s) :
    cast (congrArg M.carrier h.symm) x = y ↔
      x = cast (congrArg M.carrier h) y := by
  cases h
  rfl

theorem Model.pullback_lift {k l : Nat} {Γ : Fin k → S} {Δ : Fin l → S}
    (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i) (bound : S)
    (a : (i : Fin l) → M.carrier (Δ i)) (x : M.carrier bound) :
    M.pullback (liftIndex f) (liftSort f h bound) (Fin.cases x a) =
      Fin.cases x (M.pullback f h a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Renaming changes only assignment lookup, including beneath binders. -/
theorem Model.denote_rename {k : Nat} {Γ : Fin k → S} {s : S}
    (p : Pattern A Γ s) : ∀ {l : Nat} {Δ : Fin l → S}
      (f : Fin k → Fin l) (h : ∀ i, Δ (f i) = Γ i)
      (a : (i : Fin l) → M.carrier (Δ i)),
      M.denote a (p.rename f h) = M.denote (M.pullback f h a) p := by
  induction p with
  | var i =>
      intro l Δ f h a
      ext w
      simp only [Pattern.rename, mem_denote_sort_cast, Model.denote,
        Set.mem_singleton_iff, Model.pullback]
      exact cast_eq_iff M (h i) w (a (f i))
  | app op args ih =>
      intro l Δ f h a
      simp only [Pattern.rename, Model.denote, ih]
  | neg p ih =>
      intro l Δ f h a
      exact congrArg (fun X => Xᶜ) (ih f h a)
  | conj p q ihp ihq =>
      intro l Δ f h a
      exact congrArg₂ Set.inter (ihp f h a) (ihq f h a)
  | ex bound body ih =>
      intro l Δ f h a
      ext w
      simp only [Pattern.rename, Model.denote, ih, Set.mem_ofPred_eq]
      apply exists_congr
      intro x
      rw [M.pullback_lift f h bound a x]
      rfl

/-- Native syntactic free-variable support controls semantic dependence. -/
theorem Model.denote_eq_of_agree {k : Nat} {Γ : Fin k → S} {s : S}
    (p : Pattern A Γ s) : ∀ (a b : (i : Fin k) → M.carrier (Γ i)),
    (∀ i, i ∈ p.free → a i = b i) → M.denote a p = M.denote b p := by
  induction p with
  | var i =>
      intro a b agree
      have same := agree i (by simp [Pattern.free])
      simp only [Model.denote, same]
  | app op args ih =>
      intro a b agree
      have same : ∀ i, M.denote a (args i) = M.denote b (args i) := by
        intro i
        apply ih i a b
        intro j hj
        apply agree j
        simp only [Pattern.free, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, hj⟩
      simp only [Model.denote, same]
  | neg p ih =>
      intro a b agree
      exact congrArg (fun X => Xᶜ) (ih a b agree)
  | conj p q ihp ihq =>
      intro a b agree
      exact congrArg₂ Set.inter
        (ihp a b (fun i hi => agree i (Finset.mem_union_left _ hi)))
        (ihq a b (fun i hi => agree i (Finset.mem_union_right _ hi)))
  | ex bound body ih =>
      intro a b agree
      have same : ∀ x : M.carrier bound,
          M.denote (Fin.cases x a) body = M.denote (Fin.cases x b) body := by
        intro x
        apply ih (Fin.cases x a) (Fin.cases x b)
        intro i hi
        revert hi
        refine Fin.cases ?_ (fun j => ?_) i
        · intro _
          rfl
        · intro hj
          exact agree j (by simpa only [Pattern.free, Finset.mem_filter,
            Finset.mem_univ, true_and] using hj)
      simp only [Model.denote, same]

theorem Model.pullback_close {k : Nat} {Γ : Fin k → S}
    (j : Fin k) (a : (i : Fin k) → M.carrier (Γ i)) (x : M.carrier (Γ j)) :
    M.pullback (closeIndex j) (closeSort Γ j) (Fin.cases x a) =
      Function.update a j x := by
  funext i
  unfold Model.pullback
  apply eq_of_heq
  apply HEq.trans (cast_heq _ _)
  let lookup : (z : Fin (k + 1)) →
      M.carrier ((Fin.cases (Γ j) Γ : Fin (k + 1) → S) z) := Fin.cases x a
  by_cases same : i = j
  · subst i
    rw [Function.update_self]
    have endpoint : lookup 0 = x := by rfl
    exact (dependent_congr lookup (by simp [closeIndex] : closeIndex j j = 0)).trans
      (heq_of_eq endpoint)
  · rw [Function.update_of_ne same]
    have endpoint : lookup i.succ = a i := by rfl
    exact (dependent_congr lookup (by simp [closeIndex, same] : closeIndex j i = i.succ)).trans
      (heq_of_eq endpoint)

/-- One actual native binder is exactly valuation rebinding at that coordinate. -/
theorem Model.denote_close {k : Nat} {Γ : Fin k → S} {s : S}
    (j : Fin k) (p : Pattern A Γ s) (a : (i : Fin k) → M.carrier (Γ i))
    (w : M.carrier s) : w ∈ M.denote a (p.close j) ↔
      ∃ b, (∀ i, i ≠ j → a i = b i) ∧ w ∈ M.denote b p := by
  simp only [Pattern.close, Model.denote, Model.denote_rename, Model.pullback_close]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Function.update a j x, fun i hi => (Function.update_of_ne hi x a).symm, hx⟩
  · rintro ⟨b, agree, hb⟩
    refine ⟨b j, ?_⟩
    have same : Function.update a j (b j) = b := by
      funext i
      by_cases hi : i = j
      · subst i
        simp only [Function.update_self]
      · simpa only [Function.update_of_ne hi] using agree i hi
    simpa only [Pattern.abstractList, List.foldr_nil, same] using hb

/-- Iterated native existential binders implement simultaneous finite rebinding. -/
theorem Model.denote_abstractList {k : Nat} {Γ : Fin k → S} {s : S}
    (xs : List (Fin k)) (p : Pattern A Γ s) :
    ∀ (a : (i : Fin k) → M.carrier (Γ i)) (w : M.carrier s),
      w ∈ M.denote a (p.abstractList xs) ↔
      ∃ b, (∀ i, i ∉ xs → a i = b i) ∧ w ∈ M.denote b p := by
  induction xs with
  | nil =>
      intro a w
      constructor
      · intro hw
        exact ⟨a, fun _ _ => rfl, hw⟩
      · rintro ⟨b, agree, hb⟩
        have same : a = b := funext (fun i => agree i (by simp))
        simpa only [Pattern.abstractList, List.foldr_nil, same] using hb
  | cons j xs ih =>
      intro a w
      change w ∈ M.denote a ((p.abstractList xs).close j) ↔ _
      rw [M.denote_close]
      constructor
      · rintro ⟨b, ab, hb⟩
        obtain ⟨c, bc, hc⟩ := (ih b w).mp hb
        refine ⟨c, ?_, hc⟩
        intro i hi
        have split : i ≠ j ∧ i ∉ xs := by simpa only [List.mem_cons, not_or] using hi
        exact (ab i split.1).trans (bc i split.2)
      · rintro ⟨c, ac, hc⟩
        refine ⟨Function.update a j (c j), ?_, (ih _ w).mpr ⟨c, ?_, hc⟩⟩
        · intro i hi
          exact (Function.update_of_ne hi (c j) a).symm
        · intro i hi
          by_cases same : i = j
          · subst i
            simp only [Function.update_self]
          · simpa only [Function.update_of_ne same] using
              ac i (by simp only [List.mem_cons, not_or]; exact ⟨same, hi⟩)

theorem Model.denote_abstract {k : Nat} {Γ : Fin k → S} {s : S}
    (X : Finset (Fin k)) (p : Pattern A Γ s)
    (a : (i : Fin k) → M.carrier (Γ i)) (w : M.carrier s) :
    w ∈ M.denote a (p.abstract X) ↔
      ∃ b, (∀ i, i ∉ X → a i = b i) ∧ w ∈ M.denote b p := by
  simpa only [Pattern.abstract, Finset.mem_toList] using M.denote_abstractList X.toList p a w

theorem Model.pullback_join_left {k n : Nat} {Γ : Fin k → S} {Δ : Fin n → S}
    (a : (i : Fin k) → M.carrier (Γ i)) (b : (i : Fin n) → M.carrier (Δ i)) :
    M.pullback (Fin.castAdd n) (leftSort Γ Δ) (M.joinAssignment a b) = a := by
  funext i
  simp [Model.pullback, Model.joinAssignment]

theorem Model.pullback_join_right {k n : Nat} {Γ : Fin k → S} {Δ : Fin n → S}
    (a : (i : Fin k) → M.carrier (Γ i)) (b : (i : Fin n) → M.carrier (Δ i)) :
    M.pullback (Fin.natAdd k) (rightSort Γ Δ) (M.joinAssignment a b) = b := by
  funext i
  simp [Model.pullback, Model.joinAssignment]

end Silmaril.Logic.Matching.FirstOrder
