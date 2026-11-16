module

public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.LTS.Thms

/-!
# The strategy of a handler has every limit of its plays (proofs)

The transition system of a handler has no silent steps and is deterministic: a configuration
`call m k` calls `m` and continues with `k`, a configuration `pure r` returns `r`. So the state
after a trace is unique (`run_det`), and the states after the members of an infinite play of
the handler chain into an infinite run (`ofHandler_eq_limits`). Handlers never diverge.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionRoute

open Silmaril.Games

universe u

variable {E F : Sig.{u}} {h : Handler E F}

theorem step_det {x y y' : h.toReduction.toLTS.State} {l : Option (Move E F)}
    (h₁ : h.toReduction.toLTS.step x l y) (h₂ : h.toReduction.toLTS.step x l y') : y = y' := by
  cases h₁ with
  | ask q => cases h₂; rfl
  | tau hs => exact hs.elim
  | call hc =>
    cases h₂ with
    | call hc' =>
      have := hc.symm.trans hc'
      cases this
      rfl
  | resume q m k n => cases h₂; rfl
  | ret hd => cases h₂; rfl

theorem not_silent {x y : h.toReduction.toLTS.State} : ¬ h.toReduction.toLTS.step x none y := by
  intro hs
  cases hs with
  | tau hs => exact hs

/-- The state after a trace of a handler is unique. -/
theorem run_det {x y y' : h.toReduction.toLTS.State} {s : List (Move E F)}
    (h₁ : h.toReduction.toLTS.Run x s y) (h₂ : h.toReduction.toLTS.Run x s y') : y = y' := by
  induction h₁ with
  | nil x =>
    cases h₂ with
    | nil => rfl
    | tau hs _ => exact (not_silent hs).elim
  | tau hs _ _ => exact (not_silent hs).elim
  | vis hs _ ih =>
    cases h₂ with
    | tau hs' _ => exact (not_silent hs').elim
    | vis hs' hr' =>
      cases step_det hs hs'
      exact ih hr'

/-- **A handler's strategy has no divergence and every limit of its plays.** -/
theorem ofHandler_eq_limits (h : Handler E F) :
    DStrategy.ofHandler h = DStrategy.limits (Strategy.ofHandler h) := by
  refine DStrategy.ext rfl (DStrategy.ofHandler_div h) ?_
  ext I
  constructor
  · intro hI
    exact ⟨(DStrategy.ofHandler h).inf_isInf hI, fun _ hq => (DStrategy.ofHandler h).inf_sub hI hq⟩
  · rintro ⟨hI, hsub⟩
    have hrun : ∀ n, ∃ y, h.toReduction.toLTS.Run .idle (hI.seq n) y := fun n =>
      Strategy.mem_ofHandler.1 (hsub (hI.seq_mem n))
    choose st hst using hrun
    refine ⟨⟨⟨st, hI.seq, ?_, ?_, fun n => ?_⟩, hI.seq_unbounded, hI.lim_seq.symm⟩,
      fun q hq => (Strategy.ofHandler h).legal (hsub hq)⟩
    · have h0 : hI.seq 0 = [] := List.eq_nil_of_length_eq_zero (hI.seq_length 0)
      have := hst 0
      rw [h0] at this
      exact run_det this (.nil _)
    · exact List.eq_nil_of_length_eq_zero (hI.seq_length 0)
    · obtain ⟨w, hw⟩ := hI.seq_mono n
      refine ⟨w, hw.symm, ?_⟩
      have := hst (n + 1)
      rw [← hw] at this
      obtain ⟨y, hy, hw'⟩ := LTS.Run.of_append this
      cases run_det hy (hst n)
      exact hw'

end Silmaril.Proofs.Games.Abstract.SessionRoute
