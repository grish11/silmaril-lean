module

public import Silmaril.Semantics.Brookes.Defs

public section

namespace Silmaril.Proofs.Semantics.Brookes

open Silmaril.Semantics.Brookes

universe u v

variable {Store : Type u} {A : Type v}

theorem close_extensive {seed : Trace Store → A → Prop} {trace : Trace Store} {value : A}
    (h : seed trace value) : close seed trace value :=
  ⟨trace, h, .refl trace⟩

theorem close_mono {seed covering : Trace Store → A → Prop}
    (h : ∀ ⦃trace value⦄, seed trace value → covering trace value)
    {trace value} (mem : close seed trace value) : close covering trace value := by
  obtain ⟨source, hs, hr⟩ := mem
  exact ⟨source, h hs, hr⟩

theorem close_stable {seed : Trace Store → A → Prop} {source target : Trace Store} {value : A}
    (h : close seed source value) (step : Reduces source target) : close seed target value := by
  obtain ⟨origin, hs, hr⟩ := h
  exact ⟨origin, hs, hr.trans step⟩

theorem close_least {seed covering : Trace Store → A → Prop}
    (includes : ∀ ⦃trace value⦄, seed trace value → covering trace value)
    (stable : ∀ ⦃source target value⦄, covering source value → Reduces source target →
      covering target value)
    {trace value} (mem : close seed trace value) : covering trace value := by
  obtain ⟨source, hs, hr⟩ := mem
  exact stable (includes hs) hr

theorem close_idem (seed : Trace Store → A → Prop) : close (close seed) = close seed := by
  funext trace value
  exact propext ⟨fun ⟨_, hs, hr⟩ => close_stable hs hr, close_extensive⟩

theorem reduces_append_left {source target : Trace Store}
    (h : Reduces source target) (pre : Trace Store) : Reduces (pre ++ source) (pre ++ target) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih =>
    apply ih.tail
    cases step with
    | stutter left right s =>
      simpa only [List.append_assoc] using Rewrite.stutter (pre ++ left) right s
    | mumble left right s t u =>
      simpa only [List.append_assoc] using Rewrite.mumble (pre ++ left) right s t u

theorem reduces_append_right {source target : Trace Store}
    (h : Reduces source target) (post : Trace Store) : Reduces (source ++ post) (target ++ post) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih =>
    apply ih.tail
    cases step with
    | stutter left right s =>
      simpa only [List.append_assoc, List.cons_append] using Rewrite.stutter left (right ++ post) s
    | mumble left right s t u =>
      simpa only [List.append_assoc, List.cons_append] using
        Rewrite.mumble left (right ++ post) s t u

theorem reduces_append {left left' right right' : Trace Store}
    (h₁ : Reduces left left') (h₂ : Reduces right right') :
    Reduces (left ++ right) (left' ++ right') :=
  (reduces_append_right h₁ right).trans (reduces_append_left h₂ left')

theorem behavior_ext {first second : Behavior Store A}
    (accepts : ∀ trace value, first.accepts trace value ↔ second.accepts trace value) :
    first = second := by
  cases first with
  | mk left hl sl =>
    cases second with
    | mk right hr sr =>
      have eq : left = right := funext fun trace => funext fun value => propext (accepts trace value)
      cases eq
      rfl

theorem generate_accepts {seed : Trace Store → A → Prop} {trace : Trace Store} {value : A}
    (hne : trace ≠ []) (hs : seed trace value) : (Behavior.generate seed).accepts trace value :=
  ⟨trace, ⟨hne, hs⟩, .refl trace⟩

theorem generate_eq (behavior : Behavior Store A) :
    Behavior.generate behavior.accepts = behavior := by
  apply behavior_ext
  intro trace value
  exact ⟨fun ⟨_, ⟨_, hs⟩, hr⟩ => behavior.stable hs hr,
    fun h => generate_accepts (behavior.nonempty h) h⟩

theorem runs_append {s t : Store} {left right : Trace Store} :
    Runs s (left ++ right) t ↔ ∃ m, Runs s left m ∧ Runs m right t := by
  induction left generalizing s with
  | nil =>
    constructor
    · intro h
      exact ⟨s, .nil _, h⟩
    · rintro ⟨_, h, ht⟩
      cases h
      exact ht
  | cons step steps ih =>
    rcases step with ⟨before, after⟩
    constructor
    · intro h
      cases h with
      | cons rest =>
        obtain ⟨m, hl, hr⟩ := ih.mp rest
        exact ⟨m, .cons hl, hr⟩
    · rintro ⟨m, hl, hr⟩
      cases hl with
      | cons rest => exact .cons (ih.mpr ⟨m, rest, hr⟩)

private theorem runs_of_rewrite {s t : Store} {source target : Trace Store}
    (step : Rewrite source target) (run : Runs s target t) : Runs s source t := by
  cases step with
  | stutter left right store =>
    obtain ⟨m, hl, hr⟩ := runs_append.mp run
    cases hr with
    | cons rest => exact runs_append.mpr ⟨_, hl, rest⟩
  | mumble left right before middle after =>
    obtain ⟨m, hl, hr⟩ := runs_append.mp run
    cases hr with
    | cons rest => exact runs_append.mpr ⟨_, hl, .cons (.cons rest)⟩

theorem runs_of_reduces {s t : Store} {source target : Trace Store}
    (h : Reduces source target) (run : Runs s target t) : Runs s source t := by
  induction h with
  | refl => exact run
  | tail _ step ih => exact ih (runs_of_rewrite step run)

theorem reduces_singleton_of_runs {s t : Store} {trace : Trace Store}
    (run : Runs s trace t) (hne : trace ≠ []) : Reduces trace [(s, t)] := by
  induction run with
  | nil => exact False.elim (hne rfl)
  | @cons before middle after rest run ih =>
    cases rest with
    | nil =>
      cases run
      exact .refl _
    | cons step rest =>
      have hr := reduces_append_left (ih (by simp)) [(before, middle)]
      exact hr.tail (Rewrite.mumble [] [] before middle after)

theorem completes_generate_iff {seed : Trace Store → A → Prop} {s t : Store} {value : A} :
    (Behavior.generate seed).completes s t value ↔
      ∃ trace, trace ≠ [] ∧ seed trace value ∧ Runs s trace t := by
  constructor
  · rintro ⟨trace, ⟨hne, hs⟩, hr⟩
    exact ⟨trace, hne, hs, runs_of_reduces hr (.cons (.nil t))⟩
  · rintro ⟨trace, hne, hs, run⟩
    exact ⟨trace, ⟨hne, hs⟩, reduces_singleton_of_runs run hne⟩

end Silmaril.Proofs.Semantics.Brookes
