module

public import Silmaril.Semantics.Accept.IO.Defs

/-! # Proofs: relational I/O acceptance

Proofs of `Silmaril.Semantics.Accept.IO.Thms`: characterisations of input windows and of the
runs of a trace, scope-view invariance, and transport of the relations along renamings.
-/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.IO

open Silmaril.Accept Silmaril.Accept.IO
open scoped Silmaril.Accept

universe u₁ u₂ u₃ u₄ u₅

variable {K : Type u₁} {X : Type u₂} {I : Type u₃} {O : Type u₄} {C : Type u₅}

/-! ## Input windows -/

theorem mem_windows {l : List (Loc X I O C)} {r : Run I O C} :
    r ∈ windows l ↔ ∃ pre i post, l = pre ++ .inp i :: post ∧ (∀ e ∈ pre, ¬ e.IsExit) ∧
      r = ⟨i, (collect true post).1, (collect true post).2⟩ := by
  induction l with
  | nil => simp [windows]
  | cons e l ih =>
    constructor
    · intro h
      cases e with
      | inp i =>
        rcases List.mem_cons.1 h with rfl | h
        · exact ⟨[], i, l, rfl, by simp, rfl⟩
        · obtain ⟨pre, j, post, rfl, hpre, rfl⟩ := ih.1 h
          exact ⟨.inp i :: pre, j, post, rfl, by simpa [Loc.IsExit] using hpre, rfl⟩
      | exit c => simp [windows] at h
      | out o =>
        obtain ⟨pre, j, post, rfl, hpre, rfl⟩ := ih.1 h
        exact ⟨.out o :: pre, j, post, rfl, by simpa [Loc.IsExit] using hpre, rfl⟩
      | enter x =>
        obtain ⟨pre, j, post, rfl, hpre, rfl⟩ := ih.1 h
        exact ⟨.enter x :: pre, j, post, rfl, by simpa [Loc.IsExit] using hpre, rfl⟩
    · rintro ⟨pre, i, post, hl, hpre, rfl⟩
      cases pre with
      | nil =>
        cases hl
        simp [windows]
      | cons e' pre =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj hl
        have hrest : _ ∈ windows (pre ++ .inp i :: post) :=
          ih.2 ⟨pre, i, post, rfl, fun e he => hpre e (List.mem_cons_of_mem _ he), rfl⟩
        have he' : ¬ e.IsExit := hpre e List.mem_cons_self
        cases e with
        | inp j => exact List.mem_cons_of_mem _ hrest
        | exit c => exact absurd trivial he'
        | out o => exact hrest
        | enter x => exact hrest

/-! ## Runs of a trace -/

theorem localView_eq_nil_of_not_mem [DecidableEq K] {k : K} {t : List (Ev K X I O C)}
    (hk : k ∉ scopes t) : localView k t = [] := by
  unfold localView
  rw [List.filterMap_eq_nil_iff]
  intro e he
  have : e.scope ≠ k := fun h => hk (by
    unfold scopes
    rw [List.mem_eraseDups]
    exact List.mem_map.2 ⟨e, he, h⟩)
  simp [Ev.at, this]

theorem mem_inputRuns [DecidableEq K] {t : List (Ev K X I O C)} {r : Run I O C} :
    r ∈ inputRuns t ↔ ∃ k, r ∈ windows (localView k t) := by
  unfold inputRuns
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, -, h⟩
    exact ⟨k, h⟩
  · rintro ⟨k, h⟩
    by_cases hk : k ∈ scopes t
    · exact ⟨k, hk, h⟩
    · rw [localView_eq_nil_of_not_mem hk] at h
      simp [windows] at h

theorem mem_entryRuns [DecidableEq K] {t : List (Ev K X I O C)} {r : Run X O C} :
    r ∈ entryRuns t ↔ ∃ k, entryRun (localView k t) = some r := by
  unfold entryRuns
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, -, h⟩
    exact ⟨k, h⟩
  · rintro ⟨k, h⟩
    by_cases hk : k ∈ scopes t
    · exact ⟨k, hk, h⟩
    · rw [localView_eq_nil_of_not_mem hk] at h
      simp [entryRun] at h

theorem inputRunsOf_eq [DecidableEq K] (T : Set (List (Ev K X I O C))) :
    inputRunsOf T = {r | ∃ l ∈ ScopeViews T, r ∈ windows l} := by
  ext r
  simp only [inputRunsOf, ScopeViews, Set.mem_ofPred_eq, mem_inputRuns]
  constructor
  · rintro ⟨t, ht, k, h⟩
    exact ⟨_, ⟨t, ht, k, rfl⟩, h⟩
  · rintro ⟨_, ⟨t, ht, k, rfl⟩, h⟩
    exact ⟨t, ht, k, h⟩

theorem entryRunsOf_eq [DecidableEq K] (T : Set (List (Ev K X I O C))) :
    entryRunsOf T = {r | ∃ l ∈ ScopeViews T, entryRun l = some r} := by
  ext r
  simp only [entryRunsOf, ScopeViews, Set.mem_ofPred_eq, mem_entryRuns]
  constructor
  · rintro ⟨t, ht, k, h⟩
    exact ⟨_, ⟨t, ht, k, rfl⟩, h⟩
  · rintro ⟨_, ⟨t, ht, k, rfl⟩, h⟩
    exact ⟨t, ht, k, h⟩

theorem localView_insert_other [DecidableEq K] {k : K} (u v : List (Ev K X I O C))
    {e : Ev K X I O C} (he : e.scope ≠ k) :
    localView k (u ++ e :: v) = localView k (u ++ v) := by
  simp [localView, List.filterMap_append, Ev.at, he]

theorem inputRuns_congr [DecidableEq K] {t t' : List (Ev K X I O C)}
    (h : ∀ k, localView k t = localView k t') (r : Run I O C) :
    r ∈ inputRuns t ↔ r ∈ inputRuns t' := by
  simp only [mem_inputRuns, h]

theorem entryRuns_congr [DecidableEq K] {t t' : List (Ev K X I O C)}
    (h : ∀ k, localView k t = localView k t') (r : Run X O C) :
    r ∈ entryRuns t ↔ r ∈ entryRuns t' := by
  simp only [mem_entryRuns, h]

/-! ## Relations -/

section Rel

variable {S : Set (Run I O C)}

theorem returns_eq_image (S : Set (Run I O C)) :
    returns S = (fun p => (p.1, p.2.2)) '' episodes S := by
  ext ⟨a, c⟩
  simp only [returns, Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨bs, h⟩
    exact ⟨a, bs, c, h, rfl, rfl⟩
  · rintro ⟨a', bs, c', h, rfl, rfl⟩
    exact ⟨bs, h⟩

theorem image_retTriggers_eq (hS : ∀ r ∈ S, r.result.isSome) :
    (fun p => (p.1, p.2.1)) '' retTriggers S = triggers S := by
  ext ⟨a, b⟩
  simp only [Set.mem_image, retTriggers, episodes, triggers, Set.mem_ofPred_eq, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a', b', c, ⟨bs, h, hb⟩, rfl, rfl⟩
    exact ⟨_, h, rfl, hb⟩
  · rintro ⟨r, hr, rfl, hb⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hS r hr)
    refine ⟨r.input, b, c, ⟨r.outputs, ?_, hb⟩, rfl, rfl⟩
    rw [← hc]
    exact hr

variable {I' : Type*} {O' : Type*} {C' : Type*} (f : I → I') (g : O → O') (h : C → C')

theorem triggers_image_map :
    triggers (Run.map f g h '' S) = Prod.map f g '' triggers S := by
  ext ⟨a', b'⟩
  simp only [triggers, Set.mem_image, Set.mem_ofPred_eq, Prod.exists, Prod.map, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl, hb⟩
    simp only [Run.map] at hb
    obtain ⟨b, hb₀, rfl⟩ := List.mem_map.1 hb
    exact ⟨r.input, b, ⟨r, hr, rfl, hb₀⟩, rfl, rfl⟩
  · rintro ⟨a, b, ⟨r, hr, rfl, hb⟩, rfl, rfl⟩
    exact ⟨_, ⟨r, hr, rfl⟩, rfl, List.mem_map_of_mem hb⟩

theorem episodes_image_map :
    episodes (Run.map f g h '' S) = Prod.map f (Prod.map (List.map g) h) '' episodes S := by
  ext ⟨a', bs', c'⟩
  simp only [episodes, Set.mem_image, Set.mem_ofPred_eq, Prod.exists, Prod.map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, bs, c⟩, hr, he⟩
    simp only [Run.map, Run.mk.injEq] at he
    obtain ⟨rfl, rfl, hc⟩ := he
    obtain ⟨c, rfl, rfl⟩ := Option.map_eq_some_iff.1 hc
    exact ⟨a, bs, c, hr, rfl, rfl, rfl⟩
  · rintro ⟨a, bs, c, hr, rfl, rfl, rfl⟩
    exact ⟨_, hr, rfl⟩

end Rel

end Silmaril.Proofs.Semantics.Accept.IO
