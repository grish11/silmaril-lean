module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Replay
import Mathlib.Data.List.Chain

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Normalize.Proofs

open Relation (ReflTransGen)

variable {A B : Type} [DecidableEq B] (view : A → B)

theorem changes_start (a b : A) (tail : List A) (same : view a = view b) :
    changes view a tail = changes view b tail := by
  cases tail with
  | nil => rfl
  | cons next tail => simp only [changes, same]

theorem changes_last (start : A) (tail : List A) :
    (changes view start tail).getLastD (view start) = view (tail.getLastD start) := by
  induction tail generalizing start with
  | nil => rfl
  | cons next tail ih =>
    by_cases same : view start = view next
    · simpa only [changes, same, ite_true, List.getLastD_cons] using ih next
    · simpa only [changes, ite_eq_right same, List.getLastD_cons] using ih next

theorem changes_chain {step : A → A → Prop} {step' : B → B → Prop} {final : A}
    (sim : ∀ {a b}, step a b → ReflTransGen step a final → view a = view b ∨ step' (view a) (view b))
    (start : A) (tail : List A)
    (legal : List.IsChain step (start :: tail)) (last : tail.getLastD start = final) :
    List.IsChain step' (view start :: changes view start tail) := by
  induction tail generalizing start with
  | nil => exact .singleton _
  | cons next tail ih =>
    obtain ⟨step, rest⟩ := List.isChain_cons_cons.mp legal
    rw [List.getLastD_cons] at last
    have reaches : ReflTransGen _ start final := last ▸ (Log.Proofs.reaches next tail rest).head step
    by_cases same : view start = view next
    · simp only [changes, same, ite_true]
      exact ih next rest last
    · simp only [changes, ite_eq_right same]
      exact .cons_cons ((sim step reaches).resolve_left same) (ih next rest last)

theorem changes_const (start : A) (earlier rest : List A)
    (constant : ∀ mark ∈ earlier, view mark = view start) :
    changes view start (earlier ++ rest) = changes view start rest := by
  induction earlier generalizing start with
  | nil => rfl
  | cons mark tail ih =>
    have same := constant mark (by simp)
    rw [List.cons_append, changes, ite_eq_left same.symm]
    exact (ih mark (fun x h => (constant x (List.mem_cons_of_mem _ h)).trans same.symm)).trans
      (changes_start view mark start rest same)

theorem changes_section (lift : B → A) (cancel : ∀ mark, view (lift mark) = mark)
    (start : A) (rest : List B) :
    changes view start (rest.map lift) = changes id (view start) rest := by
  induction rest generalizing start with
  | nil => rfl
  | cons mark tail ih =>
    simp only [List.map_cons, changes, cancel, id_eq, ih]

theorem changes_twice (start : A) (rest : List A) :
    changes id (view start) (changes view start rest) = changes view start rest := by
  induction rest generalizing start with
  | nil => rfl
  | cons mark tail ih =>
    by_cases same : view start = view mark
    · simp only [changes, same, ite_true, ih]
    · simp only [changes, id_eq, ite_eq_right same, ih]

theorem last_append {A : Type} (start : A) (xs ys : List A) :
    (xs ++ ys).getLastD start = ys.getLastD (xs.getLastD start) := by
  induction xs generalizing start with
  | nil => rfl
  | cons _ _ ih => simp only [List.cons_append, List.getLastD_cons, ih]

theorem chain_append {A : Type} {step : A → A → Prop} {start : A} {xs ys : List A}
    (left : List.IsChain step (start :: xs)) (right : List.IsChain step (xs.getLastD start :: ys)) :
    List.IsChain step (start :: (xs ++ ys)) := by
  induction xs generalizing start with
  | nil => exact right
  | cons _ _ ih =>
    obtain ⟨first, rest⟩ := List.isChain_cons_cons.mp left
    exact .cons_cons first (ih rest (by simpa only [List.getLastD_cons] using right))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Normalize.Proofs
