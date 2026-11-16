module

public import Silmaril.Wasm.Abstract.HostTrapS.Defs
public import Silmaril.Games.Abstract.ModuleTrap.Thms

/-!
# A trap answer ends the session run (proofs)

`evalLXPS_trapLast`: in a run of `EvalLXPS`, a call answered by a trap (`.inr ()`, the callee
trapped) is the last call, and the run ends in a trap flow. A trap answer ends the caller at
once (`callTrap`, `indTrap`, `refTrap`); a run continuing after a sub-run (an argument, a block
body, a condition, a handler body) needs that sub-run to end normally, by a branch or by a caught
exception, never by a trap; and a trap flow passes through every block, loop, conditional and
handler unchanged.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostTrapS

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- The trapped calls of the session open module. -/
abbrev PS (H : Type) : SCall H → Prop := TrapCall (sh := wasmHShapeS H) IsHostTrap (trapEndS H)

theorem ps_mk_inr {a : Nat} {args : List Val} {s s' : Store H} :
    PS H (SCall.mk a args s (.inr ()) s') := trivial

theorem not_ps_mk_inl {a : Nat} {args : List Val} {s s' : Store H} {b : List Val ⊕ Nat} :
    ¬ PS H (SCall.mk a args s (.inl b) s') := fun h => h

theorem ne_trap_of_blockVals {fl : Flow} {vs : List Val} (hvs : fl.blockVals = some vs) :
    POut.flow fl ≠ .flow .trap := by
  rintro ⟨⟩
  simp [Flow.blockVals] at hvs

/-- No trapped call in a sub-run that does not end in a trap. -/
theorem noTrap {l : List (SCall H)} {r : Store H × Frame × POut}
    (h : TrapLast (PS H) (r.2.2 = .flow .trap) l) (hr : r.2.2 ≠ .flow .trap) :
    ∀ x ∈ l, ¬ PS H x :=
  TrapLast.forall_not h hr

theorem noTrap_append {l₁ l₂ : List (SCall H)} (h₁ : ∀ x ∈ l₁, ¬ PS H x)
    (h₂ : ∀ x ∈ l₂, ¬ PS H x) : ∀ x ∈ l₁ ++ l₂, ¬ PS H x := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h₁ x hx
  · exact h₂ x hx

/-- After untrapped calls, an untrapped call and a run. -/
theorem trapLast_mid {l₁ l₂ : List (SCall H)} {x : SCall H} {Q : Prop}
    (h₁ : ∀ x ∈ l₁, ¬ PS H x) (hx : ¬ PS H x) (h₂ : TrapLast (PS H) Q l₂) :
    TrapLast (PS H) Q (l₁ ++ x :: l₂) :=
  TrapLast.append h₁ (TrapLast.cons (fun h => absurd h hx) h₂)

/-- **A trap answer ends the session run in a trap flow.** -/
theorem evalLXPS_trapLast {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f stk es l r) :
    TrapLast (PS H) (r.2.2 = .flow .trap) l := by
  induction h with
  | nil => exact trapLast_nil
  | argsAbort _ _ ih => exact ih
  | callRet _ _ _ _ ih₁ ih₂ => exact trapLast_mid (noTrap ih₁ (by simp)) not_ps_mk_inl ih₂
  | callThrow _ _ _ ih =>
    exact trapLast_concat (noTrap ih (by simp)) fun h => absurd h not_ps_mk_inl
  | callTrap _ _ _ ih => exact trapLast_concat (noTrap ih (by simp)) fun _ => rfl
  | opOk _ _ _ _ ih₁ ih₂ => exact TrapLast.append (noTrap ih₁ (by simp)) ih₂
  | opStop _ _ _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | blockOk _ _ hvs _ ih₁ ih₂ =>
    exact TrapLast.append (noTrap ih₁ (ne_trap_of_blockVals hvs)) ih₂
  | blockBrk _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | blockEsc _ _ _ ih => exact ih
  | loopOk _ _ _ ih₁ ih₂ => exact TrapLast.append (noTrap ih₁ (by simp)) ih₂
  | loopBack _ _ _ ih₁ ih₂ => exact TrapLast.append (noTrap ih₁ (by simp)) ih₂
  | loopBrk _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | loopEsc _ _ _ ih => exact ih
  | ifOk _ _ _ _ hvs _ ih₁ ih₂ ih₃ =>
    exact TrapLast.append
      (noTrap_append (noTrap ih₁ (by simp)) (noTrap ih₂ (ne_trap_of_blockVals hvs))) ih₃
  | ifBrk _ _ _ _ ih₁ ih₂ =>
    exact trapLast_of_forall (noTrap_append (noTrap ih₁ (by simp)) (noTrap ih₂ (by simp)))
  | ifEsc _ _ _ _ _ ih₁ ih₂ => exact TrapLast.append (noTrap ih₁ (by simp)) ih₂
  | ifAbort _ _ ih => exact ih
  | indRet _ _ _ _ _ _ ih₁ ih₂ => exact trapLast_mid (noTrap ih₁ (by simp)) not_ps_mk_inl ih₂
  | indThrow _ _ _ _ _ ih =>
    exact trapLast_concat (noTrap ih (by simp)) fun h => absurd h not_ps_mk_inl
  | indTrap _ _ _ _ _ ih => exact trapLast_concat (noTrap ih (by simp)) fun _ => rfl
  | indRes _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | refRet _ _ _ _ _ ih₁ ih₂ => exact trapLast_mid (noTrap ih₁ (by simp)) not_ps_mk_inl ih₂
  | refThrow _ _ _ _ ih =>
    exact trapLast_concat (noTrap ih (by simp)) fun h => absurd h not_ps_mk_inl
  | refTrap _ _ _ _ ih => exact trapLast_concat (noTrap ih (by simp)) fun _ => rfl
  | refNull _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | tail _ _ _ _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | tailRes _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | throw _ _ _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | throwRefNull _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | throwRefExn _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | tryOk _ _ hvs _ ih₁ ih₂ =>
    exact TrapLast.append (noTrap ih₁ (ne_trap_of_blockVals hvs)) ih₂
  | tryBrk _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | tryEsc _ _ _ _ ih => exact ih
  | tryCatch _ _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))
  | tryRethrow _ _ _ ih => exact trapLast_of_forall (noTrap ih (by simp))

end Silmaril.Proofs.Wasm.Abstract.HostTrapS
