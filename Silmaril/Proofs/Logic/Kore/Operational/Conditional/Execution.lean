module

public import Silmaril.Logic.Kore.Operational.Conditional.Execution.Defs
public import Silmaril.Logic.Kore.Operational.Conditional.Thms

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution

open Silmaril.Logic.Kore.Operational.Conditional
open Silmaril.Logic.Kore.Operational.Conditional.Execution

theorem fire_iff (r : Rule) (c d : Config) :
    fire r c = some d ↔ ∃ v : Valuation,
      v.x = v.capturedVal ∧ r.guard.Holds v.x ∧
      c = r.beforeConfig v ∧ d = r.afterConfig v := by
  constructor
  · intro h
    cases c with
    | mk code x k =>
      cases code with
      | nil =>
        change (none : Option Config) = some d at h
        cases h
      | cons state tail =>
        change (if state = r.before ∧ r.guard.eval x = true then
          some (⟨r.after :: tail, x, k⟩ : Config) else none) = some d at h
        split at h
        next enabled =>
          obtain ⟨hs, hg⟩ := enabled
          have hd : (⟨r.after :: tail, x, k⟩ : Config) = d := Option.some.inj h
          refine ⟨⟨tail, x, x, k⟩, rfl, hg, ?_, hd.symm⟩
          cases hs
          rfl
        next => cases h
  · rintro ⟨v, hc, hg, rfl, rfl⟩
    change (if r.before = r.before ∧ r.guard.eval v.x = true then
      some (⟨r.after :: v.tail, v.x, v.counter⟩ : Config) else none) =
        some ⟨r.after :: v.tail, v.capturedVal, v.counter⟩
    rw [ite_eq_left ⟨rfl, hg⟩, hc]

theorem mem_successors (rules : List Rule) (c d : Config) :
    d ∈ successors rules c ↔ Step rules c d := by
  rw [step_iff]
  simp only [successors, List.mem_filterMap, fire_iff]

theorem successors_nil_iff (rules : List Rule) (c : Config) :
    successors rules c = [] ↔ ∀ d, ¬ Step rules c d := by
  constructor
  · intro h d hd
    have hm := (mem_successors rules c d).2 hd
    rw [h] at hm
    exact List.not_mem_nil hm
  · intro h
    cases hs : successors rules c with
    | nil => rfl
    | cons d ds =>
      have hm : d ∈ successors rules c := by
        rw [hs]
        exact List.mem_cons_self
      exact False.elim (h d ((mem_successors rules c d).1 hm))

theorem mem_frontier (rules : List Rule) (n : Nat) (c d : Config) :
    d ∈ frontier rules n c ↔ Runs rules n c d := by
  induction n generalizing c with
  | zero =>
    constructor
    · intro h
      have hd : d = c := List.mem_singleton.1 h
      subst d
      exact .refl c
    · intro h
      cases h
      exact List.mem_singleton.2 rfl
  | succ n ih =>
    change d ∈ (successors rules c).flatMap (frontier rules n) ↔ _
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨e, he, hd⟩
      exact .next ((mem_successors rules c e).1 he) ((ih e).1 hd)
    · intro h
      cases h with
      | next he hd =>
        exact ⟨_, (mem_successors rules c _).2 he, (ih _).2 hd⟩

theorem mem_explore (rules : List Rule) (n : Nat) (c d : Config) :
    d ∈ explore rules n c ↔ ∃ k, k ≤ n ∧ Runs rules k c d := by
  change d ∈ (List.range (n + 1)).flatMap (fun k => frontier rules k c) ↔ _
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hd⟩
    exact ⟨k, Nat.le_of_lt_succ (List.mem_range.1 hk), (mem_frontier rules k c d).1 hd⟩
  · rintro ⟨k, hk, hd⟩
    exact ⟨k, List.mem_range.2 (Nat.lt_succ_of_le hk), (mem_frontier rules k c d).2 hd⟩

theorem reaches_iff_runs (rules : List Rule) (c d : Config) :
    Silmaril.Logic.Reachability.Reaches (Step rules) (fun e => e = d) c ↔
      ∃ n, Runs rules n c d := by
  constructor
  · intro h
    change Silmaril.Logic.CTL.Until (Step rules) (fun _ => True) (fun e => e = d) c at h
    induction h with
    | now hd =>
      cases hd
      exact ⟨0, .refl _⟩
    | next _ hs _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .next hs hn⟩
  · rintro ⟨n, h⟩
    induction h with
    | refl c => exact .now rfl
    | next hs _ ih => exact .next trivial hs ih

theorem reaches_iff_explore (rules : List Rule) (c d : Config) :
    Silmaril.Logic.Reachability.Reaches (Step rules) (fun e => e = d) c ↔
      ∃ n, d ∈ explore rules n c := by
  rw [reaches_iff_runs]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (mem_explore rules n c d).2 ⟨n, Nat.le_refl n, hn⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, _, hk⟩ := (mem_explore rules n c d).1 hn
    exact ⟨k, hk⟩

end Silmaril.Proofs.Logic.Kore.Operational.Conditional.Execution
