module

public import Silmaril.Logic.BrookesSC.Concrete.Observation.Defs

public section

namespace Silmaril.Proofs.Logic.BrookesSC.Concrete.Observation

open Silmaril.Logic.BrookesSC Silmaril.Logic.BrookesSC.Concrete
open Silmaril.Logic.BrookesSC.Concrete.Observation Silmaril.Semantics.Brookes

universe u

variable {W : World.{u}} {A B : Type u}

theorem observe_bind_iff (first : Behavior (Store W) A) (next : A → Behavior (Store W) B)
    (s t : Store W) (r : B) :
    observe (first.bind next) s t r ↔ ∃ m a, observe first s m a ∧ observe (next a) m t r := by
  constructor
  · intro h
    obtain ⟨_, _, a, hl, hr, hd⟩ := Behavior.bind_accepts_iff.mp h
    obtain ⟨m, leftRun, rightRun⟩ := Runs.append_iff.mp (Runs.of_reduces hd (.cons (.nil t)))
    exact ⟨m, a, first.stable hl (leftRun.reduces_singleton (first.nonempty hl)),
      (next a).stable hr (rightRun.reduces_singleton ((next a).nonempty hr))⟩
  · rintro ⟨m, a, hl, hr⟩
    exact Behavior.bind_accepts_iff.mpr
      ⟨[(s, m)], [(m, t)], a, hl, hr, .tail (.refl _) (Rewrite.mumble [] [] s m t)⟩

theorem observe_ret (a : A) (s t : Store W) (r : A) :
    observe (Behavior.ret a) s t r ↔ s = t ∧ r = a :=
  Behavior.atomic_completes_iff

variable [DecidableEq W.Cell] [DecidableEq W.Mutex] [DecidableEq W.Thread]
variable {S : Signature W}

theorem observe_eval (M : TraceModel S) (p : Program S A) :
    observe (M.eval p) = (observeModel M).eval p := by
  induction p with
  | ret a =>
    rw [eval_ret, Model.eval]
    funext s t r
    exact propext (observe_ret a s t r)
  | call op next ih =>
    rw [Model.eval, Model.eval]
    funext s t r
    apply propext
    change observe ((M.operation op).bind (fun a => M.eval (next a))) s t r ↔
      ∃ m a, (observeModel M).operation op s m a ∧ (observeModel M).eval (next a) m t r
    rw [observe_bind_iff]
    have hop : observe (M.operation op) = (observeModel M).operation op := by
      rename_i designation
      cases designation with
      | external => rfl
      | primitive p =>
        rw [Model.operation, Model.operation]
        funext s t a
        exact propext (primitive_completes_iff p s t a)
    simp only [hop, ih]

theorem observe_satisfaction (M : TraceModel S) (e : Sentence S) (h : e.Satisfies M) :
    e.Satisfies (observeModel M) := by
  intro x s t r mem
  rw [← observe_eval] at mem ⊢
  exact h x mem

end Silmaril.Proofs.Logic.BrookesSC.Concrete.Observation
