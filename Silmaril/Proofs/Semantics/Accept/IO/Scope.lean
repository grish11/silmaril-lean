module

public import Silmaril.Proofs.Semantics.Accept.IO.Basic

/-! # Proofs: scope lemmas of relational I/O acceptance

Generic facts about `collect`, `windows`, `entryRun`, `localView` and `assign`, used to trace
runs back to the events and tags they were read from. They were first proved in the Wasm and
WASI bridges (`Silmaril.Proofs.Wasm.Game.IOAccept`, `Silmaril.Proofs.Wasi.IOAccept`) and are
collected here.
-/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.IO

open Silmaril.Accept Silmaril.Accept.IO
open scoped List

universe u₁ u₂ u₃ u₄ u₅

variable {K : Type u₁} {X : Type u₂} {I : Type u₃} {O : Type u₄} {C : Type u₅}

/-! ## Runs back to local events -/

theorem out_mem_of_collect {stop : Bool} {o : O} :
    ∀ {l : List (Loc X I O C)}, o ∈ (collect stop l).1 → .out o ∈ l
  | [], h => by simp [collect] at h
  | .out o' :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (out_mem_of_collect h)
  | .exit _ :: _, h => by simp [collect] at h
  | .inp _ :: l, h => by
    cases stop
    · exact List.mem_cons_of_mem _ (out_mem_of_collect (stop := false) h)
    · simp [collect] at h
  | .enter _ :: l, h => List.mem_cons_of_mem _ (out_mem_of_collect h)

theorem exit_mem_of_collect {stop : Bool} {c : C} :
    ∀ {l : List (Loc X I O C)}, (collect stop l).2 = some c → .exit (some c) ∈ l
  | [], h => by simp [collect] at h
  | .out _ :: l, h => List.mem_cons_of_mem _ (exit_mem_of_collect h)
  | .exit _ :: _, h => by simp only [collect] at h; subst h; exact List.mem_cons_self
  | .inp _ :: l, h => by
    cases stop
    · exact List.mem_cons_of_mem _ (exit_mem_of_collect (stop := false) h)
    · simp [collect] at h
  | .enter _ :: l, h => List.mem_cons_of_mem _ (exit_mem_of_collect h)

theorem out_mem_of_windows {l : List (Loc X I O C)} {r : Run I O C} {b : O}
    (hr : r ∈ windows l) (hb : b ∈ r.outputs) : Loc.out b ∈ l := by
  obtain ⟨pre, i, post, rfl, -, rfl⟩ := mem_windows.1 hr
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (out_mem_of_collect hb))

theorem inp_mem_of_windows {l : List (Loc X I O C)} {r : Run I O C} (hr : r ∈ windows l) :
    Loc.inp r.input ∈ l := by
  obtain ⟨pre, i, post, rfl, -, rfl⟩ := mem_windows.1 hr
  simp

theorem sublist_of_windows {l : List (Loc X I O C)} {r : Run I O C} (hr : r ∈ windows l) :
    ∃ post, [.inp r.input] ++ post <+ l ∧ r.outputs = (collect true post).1 ∧
      r.result = (collect true post).2 := by
  obtain ⟨pre, i, post, rfl, -, rfl⟩ := mem_windows.1 hr
  exact ⟨post, List.sublist_append_right _ _, rfl, rfl⟩

theorem out_mem_of_entryRun {l : List (Loc X I O C)} {r : Run X O C} {b : O}
    (hr : entryRun l = some r) (hb : b ∈ r.outputs) : Loc.out b ∈ l := by
  unfold entryRun at hr
  split at hr
  · cases hr
    exact List.mem_cons_of_mem _ (out_mem_of_collect hb)
  · cases hr

/-! ## Local views back to events -/

theorem loc_of_at [DecidableEq K] {k : K} {e : Ev K X I O C} {l : Loc X I O C}
    (h : Ev.at k e = some l) : e.loc = l := by
  unfold Ev.at at h
  split at h
  · exact Option.some.inj h
  · cases h

theorem exists_out_of_mem_localView [DecidableEq K] {k : K} {t : List (Ev K X I O C)} {b : O}
    (h : Loc.out b ∈ localView k t) : ∃ k', Ev.out k' b ∈ t := by
  obtain ⟨e, he, hk⟩ := List.mem_filterMap.1 h
  have hl := loc_of_at hk
  cases e with
  | out k' o =>
    simp only [Ev.loc, Loc.out.injEq] at hl
    exact ⟨k', hl ▸ he⟩
  | _ => simp [Ev.loc] at hl

theorem exists_inp_of_mem_localView [DecidableEq K] {k : K} {t : List (Ev K X I O C)} {i : I}
    (h : Loc.inp i ∈ localView k t) : ∃ k', Ev.inp k' i ∈ t := by
  obtain ⟨e, he, hk⟩ := List.mem_filterMap.1 h
  have hl := loc_of_at hk
  cases e with
  | inp k' j =>
    simp only [Ev.loc, Loc.inp.injEq] at hl
    exact ⟨k', hl ▸ he⟩
  | _ => simp [Ev.loc] at hl

theorem localView_sublist [DecidableEq K] (k : K) (evs : List (Ev K X I O C)) :
    localView k evs <+ evs.map Ev.loc := by
  induction evs with
  | nil => simp [localView]
  | cons e evs ih =>
    by_cases h : e.scope = k
    · simp only [localView, List.filterMap_cons, Ev.at, h, ite_true, List.map_cons]
      exact ih.cons_cons _
    · simp only [localView, List.filterMap_cons, Ev.at, h, ite_false, List.map_cons]
      exact ih.cons _

/-! ## Scope assignment -/

theorem tag_mem_of_mem_assign {st : List ℕ} {n : ℕ} {ts : List (Tag X I O C)}
    {e : Ev ℕ X I O C} (h : e ∈ assign st n ts) : e.tag ∈ ts := by
  induction ts generalizing st n with
  | nil => simp [assign] at h
  | cons t ts ih =>
    cases t <;> cases st <;>
      first
      | exact List.mem_cons_of_mem _ (ih (by simpa [assign] using h))
      | (simp only [assign, List.mem_cons] at h
         rcases h with rfl | h
         · exact List.mem_cons_self
         · exact List.mem_cons_of_mem _ (ih h))

theorem assign_scope : ∀ (st : List ℕ) (n : ℕ) (ts : List (Tag X I O C)),
    ∀ e ∈ assign st n ts, e.scope ∈ st ∨ n ≤ e.scope
  | _, _, [] => by simp [assign]
  | st, n, .enter x :: ts => by
    intro e he
    simp only [assign, List.mem_cons] at he
    rcases he with rfl | he
    · exact .inr le_rfl
    · rcases assign_scope _ _ ts e he with h | h
      · rcases List.mem_cons.1 h with h | h
        · exact .inr h.ge
        · exact .inl h
      · exact .inr (by omega)
  | k :: st, n, .inp i :: ts | k :: st, n, .out i :: ts => by
    intro e he
    simp only [assign, List.mem_cons] at he
    rcases he with rfl | he
    · exact .inl List.mem_cons_self
    · rcases assign_scope _ _ ts e he with h | h
      · exact .inl h
      · exact .inr (by omega)
  | k :: st, n, .exit c :: ts => by
    intro e he
    simp only [assign, List.mem_cons] at he
    rcases he with rfl | he
    · exact .inl List.mem_cons_self
    · rcases assign_scope _ _ ts e he with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr (by omega)
  | [], n, .inp _ :: ts | [], n, .out _ :: ts | [], n, .exit _ :: ts => by
    intro e he
    rcases assign_scope _ _ ts e he with h | h
    · exact .inl h
    · exact .inr (by omega)

theorem localView_assign_lt {k n : ℕ} (hk : k < n) (ts : List (Tag X I O C)) :
    localView k (assign [] n ts) = [] := by
  refine List.filterMap_eq_nil_iff.2 fun e he => ?_
  have h := assign_scope [] n ts e he
  simp only [List.not_mem_nil, false_or] at h
  simp only [Ev.at, ite_eq_right_iff, reduceCtorEq, imp_false]
  omega

theorem assign_nil_append {pre post : List (Tag X I O C)} (hpre : ∀ y, Tag.enter y ∉ pre)
    (n : ℕ) : assign [] n (pre ++ post) = assign [] (n + pre.length) post := by
  induction pre generalizing n with
  | nil => rfl
  | cons t pre ih =>
    have hpre' : ∀ y, Tag.enter y ∉ pre := fun y hy => hpre y (List.mem_cons_of_mem _ hy)
    cases t with
    | enter y => exact absurd List.mem_cons_self (hpre y)
    | _ =>
      simp only [List.cons_append, assign, ih hpre', List.length_cons]
      congr 1
      omega

theorem map_loc_assign_sublist : ∀ (st : List ℕ) (n : ℕ) (ts : List (Tag X I O C)),
    (assign st n ts).map Ev.loc <+ ts.map Tag.loc
  | _, _, [] => by simp [assign]
  | st, n, .enter x :: ts => (map_loc_assign_sublist _ _ ts).cons_cons _
  | k :: st, n, .inp i :: ts => (map_loc_assign_sublist _ _ ts).cons_cons _
  | k :: st, n, .out o :: ts => (map_loc_assign_sublist _ _ ts).cons_cons _
  | k :: st, n, .exit c :: ts => (map_loc_assign_sublist _ _ ts).cons_cons _
  | [], n, .inp _ :: ts | [], n, .out _ :: ts | [], n, .exit _ :: ts =>
    (map_loc_assign_sublist _ _ ts).cons _

end Silmaril.Proofs.Semantics.Accept.IO
