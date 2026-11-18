module

public import Silmaril.Wasm.Cfg.ExamplePending.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Proofs.Wasm.Cfg.MachineLPend

@[expose] public section

/-!
# Pending, trap-answered and exception-answered calls (regression fixtures, proofs)
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExamplePending

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.MachineL Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Cfg.ExamplePending
open Silmaril.Wasm.Abstract (EvalLXPS SCall ReachLXPS)
open Silmaril.Wasm.Cfg.Proofs.MachineLPend (trapEntry)

theorem har {f : Frame} : arity f .empty = some (0, 0) := rfl

variable {H : Type} {s s' : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}
  (hfi : s.func? f ⟨0⟩ = some (a, fi))
  (hty : Validation.DefType.funcType? fi.type = some ([], []))
include hfi hty

/-- **Pending** inside the handler. -/
theorem call_pending : ReachLXPS s f [] (liftInstrs bodyCall) [] ⟨a, ([], s)⟩ :=
  .handler har (.call .nil hfi hty)

/-- **Answered by an exception**: the handler catches it, a branch to the function label. -/
theorem call_throw (t : Nat) :
    EvalLXPS s f [] (liftInstrs bodyCall) [SCall.mk a [] s (.inl (.inr t)) s']
      (s', f, .flow (.brk 0 [])) := by
  show EvalLXPS s f [] [.tryTable .empty [.catchAll l0] [.op (.call ⟨0⟩) []]] _ _
  exact EvalLXPS.tryCatch (stk := []) har
    (EvalLXPS.callThrow (es := []) (stk := []) (t := t) (s₂ := s') .nil hfi hty) .catchAll

/-- **Answered by a callee trap**: no handler catches it; the body traps in the trap's store. -/
theorem call_trap :
    EvalLXPS s f [] (liftInstrs bodyCall) [trapEntry ⟨a, ([], s)⟩ s'] (s', f, .flow .trap) := by
  show EvalLXPS s f [] [.tryTable .empty [.catchAll l0] [.op (.call ⟨0⟩) []]] _ _
  exact EvalLXPS.tryEsc (stk := []) har
    (EvalLXPS.callTrap (es := []) (stk := []) (s₂ := s') .nil hfi hty)
    (show Abstract.CallXP.POut.Escapes (.flow .trap) from trivial) trivial

/-! ## The machine -/

/-- The pending call is a pending call of the logged machine (`MachineL.pending_iff`). -/
theorem call_pending_machine :
    ∃ (st : Machine.MState H) (l₁ l₂ : List (SCall H)),
      MRunL bodyCall (Machine.initial bodyCall s f) l₁ st ∧ ReachL bodyCall st l₂ ⟨a, ([], s)⟩ ∧
        ([] : List (SCall H)) = l₁ ++ l₂ :=
  pending_iff.mp (call_pending hfi hty)

/-- The exception-answered call: the machine runs to `exit` (the caught branch). -/
theorem call_throw_machine (t : Nat) :
    ∃ st : Machine.MState H, MRunL bodyCall (Machine.initial bodyCall s f)
      [SCall.mk a [] s (.inl (.inr t)) s'] st ∧ st.node.IsSink ∧ EndRel st (s', f, .flow (.brk 0 [])) := by
  obtain ⟨st, l₁, l₂, hr, hl, hend⟩ := backward (call_throw hfi hty t) (by simp)
  rcases hend with ⟨hs, rfl, hE⟩ | ht
  · rw [List.append_nil] at hl; subst hl; exact ⟨st, hr, hs, hE⟩
  · cases ht

/-- The trap-answered call: the machine runs to `trap`, keeping the trap's store. -/
theorem call_trap_machine :
    ∃ st : Machine.MState H, MRunL bodyCall (Machine.initial bodyCall s f)
      [trapEntry ⟨a, ([], s)⟩ s'] st ∧ st.node.IsSink ∧ EndRel st (s', f, .flow .trap) := by
  obtain ⟨st, l₁, l₂, hr, hl, hend⟩ := backward (call_trap hfi hty) (by simp)
  rcases hend with ⟨hs, rfl, hE⟩ | ht
  · rw [List.append_nil] at hl; subst hl; exact ⟨st, hr, hs, hE⟩
  · cases ht

omit hfi in
/-- **A tail call inside a handler** passes it: the body ends in a pending tail call. -/
theorem tail_handler (hfa : s.funcs[a]? = some fi) (hfi : s.func? f ⟨0⟩ = some (a, fi)) :
    EvalLXPS s f [] (liftInstrs bodyTail) [] (s, f, .tail a [] 0) := by
  show EvalLXPS s f [] [.tryTable .empty [.catchAll l0] [.op (.returnCall ⟨0⟩) []]] _ _
  exact EvalLXPS.tryEsc (stk := []) har
    (EvalLXPS.tail (es := []) (stk := []) (ps := []) (rs := []) .nil (.direct hfi) hfa hty
      (fun _ h => by simp [Abstract.CallXT.tailAnn] at h))
    (show Abstract.CallXP.POut.Escapes (.tail a [] 0) from trivial) trivial

omit hfi in
/-- The machine ends the tail-call body at the pending tail call, not at a sink. -/
theorem tail_handler_machine (hfa : s.funcs[a]? = some fi) (hfi : s.func? f ⟨0⟩ = some (a, fi)) :
    ∃ (st : Machine.MState H) (l₁ l₂ : List (SCall H)),
      MRunL bodyTail (Machine.initial bodyTail s f) l₁ st ∧ TailL bodyTail st l₂ (s, f, .tail a [] 0) := by
  obtain ⟨st, l₁, l₂, hr, -, hend⟩ := backward (tail_handler hty hfa hfi) (by simp)
  rcases hend with ⟨-, -, hE⟩ | ht
  · obtain ⟨node, stk, ls, s₀, f₀⟩ := st
    cases node <;> simp [EndRel] at hE
  · exact ⟨st, l₁, l₂, hr, ht⟩

end Silmaril.Wasm.Cfg.Proofs.ExamplePending
