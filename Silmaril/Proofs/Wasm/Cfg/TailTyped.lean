module

public import Silmaril.Wasm.Execution.Core.Sim.TypedBlock
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.Execution.Core.Soundness.PresCall
public import Silmaril.Wasm.Execution.Core.Soundness.RefTyping
public import Silmaril.Wasm.Execution.Core.Sim.TypedProgress
public import Silmaril.Wasm.Cfg.Region.Defs

@[expose] public section

/-!
# The function reference of a typed `return_call_ref`

In a typed fragment (`Sim.ContextTyped`, typed from the empty operand stack), a
`return_call_ref` (either representation, `Admin.IsReturnCallRef`) after the values `vs` has
its function reference as the last of `vs` (`retRef_ref_of_typed`): the instruction's operand
type ends in a reference type, and the values preceding it supply all of its operands.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core.PC in
/-- **A typed `return_call_ref` has its function reference last among the values before it.** -/
theorem retRef_ref_of_typed {H : Type} {s : Store H} {f : Frame} {vs : List Val} {c : Admin}
    {rest : List Admin} (h : Sim.ContextTyped ⟨s, f, vals vs ++ c :: rest⟩)
    (hcr : c.IsReturnCallRef) : ∃ W r, vs = W ++ [Val.ref r] := by
  have h1 : Sim.ContextTyped ⟨s, f, vals vs ++ [c]⟩ :=
    Sim.ContextTyped.suffix (rest := rest) (by simpa using h)
  obtain ⟨C, ts, xs, -, hC, -, hcode⟩ := h1.fragment_types
  obtain ⟨tvs, it₀, M, T, hc0, hvs, hsub, hM, hT, hMs, hP, -⟩ :=
    redex_rep hC (returnCallRef_inits hcr) hcode
  obtain ⟨d, ps, rs, rs', t₃, t₄, -, -, -, -, rfl, -, -⟩ := inv_returnCallRef hcr hc0
  have hall : ResultSub C.toTypeCtx tvs
      (((T ++ t₃) ++ ps.toList) ++ [Ty.refT true (Ty.defHeap d)]) := by
    have := ResultSub.trans hC.types hM hsub hMs
    simpa using this
  have hne : vs ≠ [] := by
    rintro rfl
    cases hvs
    have := hall.length_eq
    simp at this
  obtain ⟨W, v, rfl⟩ : ∃ W v, vs = W ++ [v] :=
    ⟨vs.dropLast, vs.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  obtain ⟨tW, tv, rfl, -, htv⟩ := PC.forall₂_split_left hvs
  obtain ⟨-, htrs⟩ := PC.forall₂_append_eq_len hall (by cases htv with | cons _ hn => cases hn; rfl)
  obtain ⟨t, rfl, ht⟩ : ∃ t, tv = [t] ∧ ValOk s v t := by
    cases htv with | cons h hnil => cases hnil; exact ⟨_, rfl, h⟩
  have hst : Sub C.toTypeCtx t (Ty.refT true (Ty.defHeap d)) := by
    cases htrs with | cons h _ => exact h
  obtain ⟨r, -, rfl, -, -⟩ := ValOk.ref_invRT ht hst
  exact ⟨W, r, rfl⟩

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Cfg.Region in
/-- Typing descends to the code of a label or handler on the redex path. -/
theorem redexIn_typed {H : Type} {s : Store H} {f : Frame} {code X : List Admin}
    (h : RedexIn code X) (hT : Sim.ContextTyped ⟨s, f, code⟩) : Sim.ContextTyped ⟨s, f, X⟩ := by
  induction h with
  | label => exact Sim.ContextTyped.label (by simpa using hT)
  | handler => exact Sim.ContextTyped.handler (by simpa using hT)
  | deepLabel _ ih => exact ih (Sim.ContextTyped.label (by simpa using hT))
  | deepHandler _ ih => exact ih (Sim.ContextTyped.handler (by simpa using hT))

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Cfg.Region in
/-- **Typed code has its pending tail calls well placed.** -/
theorem tailWF_of_typed {H : Type} {s : Store H} {f : Frame} {code : List Admin}
    (hT : Sim.ContextTyped ⟨s, f, code⟩) : TailWF code := by
  intro X hX vs c rest hXe hc
  subst hXe
  exact retRef_ref_of_typed (redexIn_typed hX hT) hc

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Cfg.Region in
/-- **From a typed start, pending tail calls stay well placed along host-free runs.** -/
theorem tailsOk_of_typed {H : Type} {P : Numerics.Profile} {c₀ : Config H}
    (hT : Sim.ContextTyped c₀) : TailsOk P (fun _ _ _ _ => False) c₀ := by
  intro c₂ h
  obtain ⟨s₂, f₂, code₂⟩ := c₂
  exact tailWF_of_typed (hT.steps h)

end Silmaril.Wasm.Cfg.Proofs.Region
