module

public import Silmaril.Semantics.Brookes.Defs
import Silmaril.Proofs.Semantics.Brookes.Closure

public section

namespace Silmaril.Proofs.Semantics.Brookes

open Silmaril.Semantics.Brookes

universe u v w z

variable {Store : Type u} {A : Type v} {B : Type w} {C : Type z}

theorem atomic_accepts_iff {step : Store → Store → A → Prop} {trace : Trace Store} {value : A} :
    (Behavior.atomic step).accepts trace value ↔
      ∃ s t, step s t value ∧ Reduces [(s, t)] trace := by
  constructor
  · rintro ⟨_, ⟨_, s, t, rfl, hs⟩, hr⟩
    exact ⟨s, t, hs, hr⟩
  · rintro ⟨s, t, hs, hr⟩
    exact ⟨[(s, t)], ⟨by simp, s, t, rfl, hs⟩, hr⟩

theorem atomic_completes_iff {step : Store → Store → A → Prop} {s t : Store} {value : A} :
    (Behavior.atomic step).completes s t value ↔ step s t value := by
  change (Behavior.atomic step).accepts [(s, t)] value ↔ step s t value
  rw [atomic_accepts_iff]
  constructor
  · rintro ⟨_, _, hs, hr⟩
    have run := runs_of_reduces hr (Runs.cons (Runs.nil t))
    cases run with
    | cons rest =>
      cases rest
      exact hs
  · exact fun hs => ⟨s, t, hs, .refl _⟩

theorem ret_accepts_iff {value result : A} {trace : Trace Store} :
    (Behavior.ret value).accepts trace result ↔
      ∃ s, result = value ∧ Reduces [(s, s)] trace := by
  rw [Behavior.ret, atomic_accepts_iff]
  exact ⟨fun ⟨s, _, ⟨rfl, h⟩, hr⟩ => ⟨s, h, hr⟩,
    fun ⟨s, h, hr⟩ => ⟨s, s, ⟨rfl, h⟩, hr⟩⟩

theorem bind_accepts_iff {first : Behavior Store A} {next : A → Behavior Store B}
    {trace : Trace Store} {result : B} :
    (first.bind next).accepts trace result ↔
      ∃ left right value, first.accepts left value ∧ (next value).accepts right result ∧
        Reduces (left ++ right) trace := by
  constructor
  · rintro ⟨_, ⟨_, left, right, value, hl, hr, rfl⟩, h⟩
    exact ⟨left, right, value, hl, hr, h⟩
  · rintro ⟨left, right, value, hl, hr, h⟩
    refine ⟨left ++ right, ⟨?_, left, right, value, hl, hr, rfl⟩, h⟩
    simp [first.nonempty hl]

theorem ret_bind (value : A) (next : A → Behavior Store B) :
    (Behavior.ret value).bind next = next value := by
  apply behavior_ext
  intro trace result
  rw [bind_accepts_iff]
  constructor
  · rintro ⟨left, right, initial, hl, hr, hd⟩
    obtain ⟨s, hValue, hs⟩ := ret_accepts_iff.mp hl
    subst initial
    have withStutter := (next value).stable hr
      (.tail (.refl _) (Rewrite.stutter [] right s))
    exact (next value).stable withStutter (Reduces.trans (reduces_append_right hs right) hd)
  · intro h
    have hne := (next value).nonempty h
    cases trace with
    | nil => exact False.elim (hne rfl)
    | cons step rest =>
      rcases step with ⟨s, t⟩
      exact ⟨[(s, s)], _, value, ret_accepts_iff.mpr ⟨s, rfl, .refl _⟩, h,
        .tail (.refl _) (Rewrite.mumble [] rest s s t)⟩

theorem bind_ret (first : Behavior Store A) : first.bind Behavior.ret = first := by
  apply behavior_ext
  intro trace result
  rw [bind_accepts_iff]
  constructor
  · rintro ⟨left, right, value, hl, hr, hd⟩
    obtain ⟨s, rfl, hs⟩ := ret_accepts_iff.mp hr
    have insert : Reduces left (left ++ [(s, s)]) := by
      simpa only [List.append_nil] using
        Reduces.tail (.refl _) (Rewrite.stutter left [] s)
    exact first.stable hl (Reduces.trans insert (Reduces.trans (reduces_append_left hs left) hd))
  · intro h
    have hne := first.nonempty h
    rcases he : trace.getLast hne with ⟨s, t⟩
    have split : trace.dropLast ++ [(s, t)] = trace :=
      he ▸ List.dropLast_concat_getLast hne
    refine ⟨trace, [(t, t)], result, h, ret_accepts_iff.mpr ⟨t, rfl, .refl _⟩, ?_⟩
    have merge : Reduces ((trace.dropLast ++ [(s, t)]) ++ [(t, t)])
        (trace.dropLast ++ [(s, t)]) := by
      rw [List.append_assoc]
      exact .tail (.refl _) (Rewrite.mumble trace.dropLast [] s t t)
    simpa only [split] using merge

theorem bind_assoc (first : Behavior Store A) (next : A → Behavior Store B)
    (last : B → Behavior Store C) :
    (first.bind next).bind last = first.bind (fun value => (next value).bind last) := by
  apply behavior_ext
  intro trace result
  simp only [bind_accepts_iff]
  constructor
  · rintro ⟨left, right, middle, ⟨one, two, initial, h₁, h₂, hleft⟩, h₃, hfinal⟩
    refine ⟨one, two ++ right, initial, h₁, ⟨two, right, middle, h₂, h₃, .refl _⟩, ?_⟩
    rw [← List.append_assoc]
    exact Reduces.trans (reduces_append_right hleft right) hfinal
  · rintro ⟨left, right, initial, h₁, ⟨two, three, middle, h₂, h₃, hright⟩, hfinal⟩
    refine ⟨left ++ two, three, middle, ⟨left, two, initial, h₁, h₂, .refl _⟩, h₃, ?_⟩
    rw [List.append_assoc]
    exact Reduces.trans (reduces_append_left hright left) hfinal

theorem forget_bind_const (first : Behavior Store A) (second : Behavior Store B) :
    (first.bind (fun _ => second)).forget = Command.seq first.forget second.forget := by
  apply behavior_ext
  intro trace result
  cases result
  change (∃ value, (first.bind (fun _ => second)).accepts trace value) ↔
      (first.forget.bind (fun _ => second.forget)).accepts trace ()
  simp only [bind_accepts_iff]
  constructor
  · rintro ⟨b, left, right, a, hl, hr, h⟩
    exact ⟨left, right, (), ⟨a, hl⟩, ⟨b, hr⟩, h⟩
  · rintro ⟨left, right, _, ⟨a, hl⟩, ⟨b, hr⟩, h⟩
    exact ⟨b, left, right, a, hl, hr, h⟩

theorem seq_completes_iff {first second : Command Store} {s t : Store} :
    (Command.seq first second).completes s t () ↔
      ∃ middle, first.completes s middle () ∧ second.completes middle t () := by
  constructor
  · intro h
    obtain ⟨_, _, value, hl, hr, hd⟩ := bind_accepts_iff.mp h
    cases value
    obtain ⟨middle, leftRun, rightRun⟩ := runs_append.mp (runs_of_reduces hd (.cons (.nil t)))
    exact ⟨middle, first.stable hl (reduces_singleton_of_runs leftRun (first.nonempty hl)),
      second.stable hr (reduces_singleton_of_runs rightRun (second.nonempty hr))⟩
  · rintro ⟨middle, hl, hr⟩
    exact bind_accepts_iff.mpr ⟨[(s, middle)], [(middle, t)], (), hl, hr,
      .tail (.refl _) (Rewrite.mumble [] [] s middle t)⟩

end Silmaril.Proofs.Semantics.Brookes
