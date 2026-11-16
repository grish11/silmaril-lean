module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Stock.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.FirstOrder.Variables
variable {Sg : FOL.Signature}
namespace Embedding
variable {k : Nat} {Γ : Fin k → Sg.S}

theorem name_injective (e : Embedding Γ) : Function.Injective e.name := by
  intro i j h
  exact e.injective (congrArg Prod.snd h)

theorem extend_name_old (e : Embedding Γ) (s : Sg.S) (i : Fin k) :
    (e.extend s).name i.succ = e.name i := rfl

theorem fresh_name_ne_old (e : Embedding Γ) (s : Sg.S) (i : Fin k) :
    (s, e.fresh) ≠ e.name i := by
  intro h
  have same := congrArg Prod.snd h
  have bound := e.tag_lt_fresh i
  change e.fresh = e.tag i at same
  omega

/-- Adding a whole block preserves every old numeric tag exactly. -/
theorem extendBlock_tag_old (e : Embedding Γ) (xs : List Sg.S) (i : Fin k) :
    (e.extendBlock xs).tag (outerIndex xs i) = e.tag i := by
  induction xs with
  | nil => rfl
  | cons s xs ih => exact ih

/-- Old sorted names, not only their numeric tags, are preserved exactly. -/
theorem extendBlock_name_old (e : Embedding Γ) (xs : List Sg.S) (i : Fin k) :
    (e.extendBlock xs).name (outerIndex xs i) = e.name i := by
  apply Prod.ext
  · exact outerSort Γ xs i
  · exact e.extendBlock_tag_old xs i

/-- Every newly allocated name is a real coordinate of the extended embedding. -/
theorem freshNames_in_range (e : Embedding Γ) (xs : List Sg.S) :
    ∀ j ∈ e.freshNames xs, ∃ i, (e.extendBlock xs).name i = j := by
  classical
  induction xs with
  | nil => simp [freshNames]
  | cons s xs ih =>
    intro j hj
    simp only [freshNames, Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact ⟨(0 : Fin (blockSize xs k + 1)), rfl⟩
    · obtain ⟨i, hi⟩ := ih j hj
      exact ⟨i.succ, hi⟩

/-- Fresh block allocation is disjoint from every old captured stock name. -/
theorem freshNames_not_old (e : Embedding Γ) (xs : List Sg.S) (i : Fin k) :
    e.name i ∉ e.freshNames xs := by
  classical
  induction xs with
  | nil => simp [freshNames]
  | cons s xs ih =>
    intro h
    simp only [freshNames, Finset.mem_insert] at h
    rcases h with h | h
    · have same := e.extendBlock_name_old xs i
      have bad := (e.extendBlock xs).fresh_name_ne_old s (outerIndex xs i)
      exact bad (h.symm.trans same.symm)
    · exact ih h

theorem freshNames_disjoint_old (e : Embedding Γ) (xs : List Sg.S) :
    Disjoint (↑(e.freshNames xs) : Set (StockName Sg)) (Set.range e.name) := by
  rw [Set.disjoint_left]
  intro j hj hold
  obtain ⟨i, rfl⟩ := hold
  exact e.freshNames_not_old xs i hj

/-- Each extended coordinate is either newly captured or an original coordinate. -/
theorem extended_name_cases (e : Embedding Γ) (xs : List Sg.S) :
    ∀ i, (e.extendBlock xs).name i ∈ e.freshNames xs ∨
      ∃ j, (e.extendBlock xs).name i = e.name j := by
  classical
  induction xs with
  | nil => intro i; exact Or.inr ⟨i, rfl⟩
  | cons s xs ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · apply Or.inl
      change (s, (e.extendBlock xs).fresh) ∈
        insert (s, (e.extendBlock xs).fresh) (e.freshNames xs)
      exact Finset.mem_insert_self _ _
    · rcases ih j with hj | ⟨l, hl⟩
      · apply Or.inl
        change (e.extendBlock xs).name j ∈
          insert (s, (e.extendBlock xs).fresh) (e.freshNames xs)
        exact Finset.mem_insert_of_mem hj
      · exact Or.inr ⟨l, hl⟩

/-- Stock assignment projection agrees exactly with a separately valued block
and the original outer assignment. No carrier nonemptiness is needed. -/
theorem assignment_extendBlock (e : Embedding Γ) (M : FOL.Structure Sg)
    (a : StockAssignment M) (xs : List Sg.S) :
    (e.extendBlock xs).assignment M a =
      joinAssignment M (e.assignment M a) xs (e.blockAssignment M a xs) := by
  induction xs with
  | nil => rfl
  | cons s xs ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun ih j

/-- Changing one freshly allocated coordinate leaves all old projections exact. -/
noncomputable def rebind (e : Embedding Γ) (M : FOL.Structure Sg) (s : Sg.S)
    (a : StockAssignment M) (x : M.carrier s) : StockAssignment M := by
  classical
  exact Function.update a (s, e.fresh) x

theorem rebind_old (e : Embedding Γ) (M : FOL.Structure Sg) (s : Sg.S)
    (a : StockAssignment M) (x : M.carrier s) :
    e.assignment M (e.rebind M s a x) = e.assignment M a := by
  classical
  funext i
  exact Function.update_of_ne (e.fresh_name_ne_old s i).symm x a

theorem rebind_fresh (e : Embedding Γ) (M : FOL.Structure Sg) (s : Sg.S)
    (a : StockAssignment M) (x : M.carrier s) :
    (e.rebind M s a x) (s, e.fresh) = x := by
  classical
  exact Function.update_self (s, e.fresh) x a

end Embedding

/-- Actual syntactic block weakening ignores exactly the new stock captures;
the separately supplied current configuration w is unchanged. -/
theorem Pattern.holds_weakenBlock {cfg : Sg.S} {k : Nat} {Γ : Fin k → Sg.S}
    (p : Pattern Sg cfg Γ) (M : FOL.Structure Sg) (e : Embedding Γ)
    (a : StockAssignment M) (w : M.carrier cfg) (xs : List Sg.S) :
    Pattern.holds (weakenBlock cfg Γ xs p) M (e.extendBlock xs) a w ↔
      Pattern.holds p M e a w := by
  unfold Pattern.holds
  rw [e.assignment_extendBlock M a xs]
  exact weakenBlock_holds M cfg Γ xs p w (e.assignment M a) (e.blockAssignment M a xs)

end Silmaril.Logic.Reachability.Derivation.FirstOrder
