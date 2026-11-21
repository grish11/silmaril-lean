module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Sentinel.Defs

/-!
# Traces of writes and export calls accept nothing

`run_writeOrEnter`: without undefined writes (`onWrite ≠ ub`), a run of the writer host (store
semantics) from a state that is not `chaos`, along a trace of writes and export calls only, accepts
nothing; `accepts_writeOrEnter` for the initial state. A sentinel-testing module whose first
write fails returns before any `accept`, so its decoded trace is of this form.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept.Writers.Sentinel

variable {Op X H : Type} [DecidableEq H] {W : Writer Op X} {pol : Policy H}

theorem run_writeOrEnter (hw : pol.onWrite ≠ .ub) {s : WState H X} {t : List (WEv Op H)}
    {s' : WState H X} {A : Set X} (hr : (writer W pol).Run s t s' A) :
    s.phase ≠ .chaos → (∀ e ∈ t, writeOrEnter e = true) → A = ∅ := by
  induction hr with
  | nil => intro _ _; rfl
  | @cons s s₁ s₂ e es A B hstep _ ih =>
    intro hs ht
    have he := ht e (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ es, writeOrEnter e' = true := fun e' h => ht e' (List.mem_cons_of_mem _ h)
    have key : A = ∅ ∧ s₁.phase ≠ .chaos := by
      cases hstep with
      | writeOk => exact ⟨rfl, nofun⟩
      | writeFail => exact ⟨rfl, nofun⟩
      | writeChaos _ hu => exact absurd hu hw
      | writeFixed _ _ hf => cases hf
      | enter => exact ⟨rfl, nofun⟩
      | resume => exact ⟨rfl, nofun⟩
      | chaos => exact absurd rfl hs
      | acceptOk => cases he
      | acceptCallTrap => cases he
      | acceptSessionTrap => cases he
      | acceptIgnore => cases he
      | acceptChaos => cases he
      | acceptFixed => cases he
      | acceptErrOk => cases he
      | acceptErrBad => cases he
      | acceptAll => cases he
      | acceptBatch => cases he
    rw [key.1, ih key.2 hrest, Set.empty_union]

/-- **A trace of writes and export calls accepts nothing** (no undefined writes). -/
theorem accepts_writeOrEnter (hw : pol.onWrite ≠ .ub) {t : List (WEv Op H)}
    (ht : ∀ e ∈ t, writeOrEnter e = true) : (writer W pol).accepts t = ∅ := by
  ext x
  simp only [Host.accepts, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨s, A, hr, hx⟩
  rw [run_writeOrEnter hw hr nofun ht] at hx
  exact hx

end Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel
