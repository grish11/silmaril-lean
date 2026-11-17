module

public import Silmaril.Wasm.Cfg.BridgeCfg.Thms
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Abstract.CallXP.Thms
public import Silmaril.Wasm.Abstract.CallXE.Thms

@[expose] public section

/-!
# Run-level projection of the logged machine to `MStepC` (proofs)

`project_sink_closedX` composes `MachineL.forward_sink`, `MachineL.closed_iff_logged`,
`CallXP.evalOXP_iff_evalOXE`, `CallXE.evalOXE_iff_evalOX` and `Bridge.native_machine_closedX`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProj

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.Bridge Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (SCall)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- A sink's native result is a flow, and not a branch past the function label. -/
theorem endRel_flow {st : MState H} {r : Store H × Frame × POut} (h : EndRel st r) :
    ∃ s₂ f₂ fl, r = (s₂, f₂, .flow fl) ∧ ∀ k vs, fl ≠ .brk (k + 1) vs := by
  unfold EndRel at h
  split at h
  · obtain ⟨fl, rfl, hv⟩ := h
    refine ⟨_, _, fl, rfl, fun k vs hfl => ?_⟩
    subst hfl; simp [Flow.retVals] at hv
  · subst h; exact ⟨_, _, _, rfl, fun _ _ h => by cases h⟩
  · obtain ⟨a, -, rfl⟩ := h; exact ⟨_, _, _, rfl, fun _ _ h => by cases h⟩
  · exact h.elim

theorem project_sink_closedX (P : Numerics.Profile) {body : Expr} {s : Store H} {f : Frame}
    {l : List (SCall H)} {st : MState H} (h : MRunL body (initial body s f) l st)
    (hs : st.node.IsSink) (hl : ∀ e ∈ l, CloseOk closedXOk e)
    (ht : Interp.TypedT s f [] (liftInstrs body))
    (hx : Abstract.CallX.xFreeL (liftInstrs body) = true)
    (he : Abstract.CallXE.ehFreeL (liftInstrs body) = true) :
    ∃ (s₂ : Store H) (f₂ : Frame) (fl : Flow) (s' : Store H) (f' : Frame) (o : Region.Out)
      (st' : MState H), EndRel st (s₂, f₂, .flow fl) ∧ ResOut closedXOk s' f' o (s₂, f₂, fl) ∧
      Relation.ReflTransGen (MStepC P Interp.noHostX closedXOk body) (initial body s f) st' ∧
      EndsC closedXOk st' s' f' o := by
  obtain ⟨r, hr, hE⟩ := forward_sink h hs
  obtain ⟨s₂, f₂, fl, rfl, hnb⟩ := endRel_flow hE
  have hp := (closed_iff_logged (C := closedXOk)).2 ⟨l, hr, hl⟩
  have hox := (Abstract.CallXE.evalOXE_iff_evalOX he).1
    ((Abstract.CallXP.evalOXP_iff_evalOXE hx).1 hp)
  obtain ⟨s', f', o, hres, hm⟩ := native_machine_closedX P hox ht
  rw [lowerList_liftInstrs] at hm
  rcases hm with ⟨k, us, hk, rfl⟩ | ⟨st', hrun, hend⟩
  · exfalso
    obtain ⟨-, -, hfr⟩ := hres
    cases fl with
    | brk k' vs =>
      obtain ⟨rfl, -⟩ := hfr
      obtain ⟨k'', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      exact hnb k'' vs rfl
    | _ => exact hfr.elim
  · exact ⟨s₂, f₂, fl, s', f', o, st', hE, hres, hrun, hend⟩

end Silmaril.Wasm.Cfg.Proofs.MachineLProj
