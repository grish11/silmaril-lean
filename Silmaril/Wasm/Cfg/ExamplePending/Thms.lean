module

public import Silmaril.Wasm.Cfg.ExamplePending.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
import Silmaril.Proofs.Wasm.Cfg.ExamplePending

@[expose] public section

/-!
# Pending, trap-answered and exception-answered calls (regression fixtures)

In a store where `call 0` resolves to the function `fi` at `a`, of type `[] → []`, the call inside
`try_table (catch_all 0)` (`bodyCall`) is, natively and on the logged machine:

* `call_pending`, `call_pending_machine`: **pending** (no answer yet), at the handler's body;
* `call_throw`, `call_throw_machine`: **answered by an exception**, which the handler catches: a
  branch to the function label, the machine at `exit`;
* `call_trap`, `call_trap_machine`: **answered by a callee trap**, which no handler catches: a trap
  in the trap's store, the machine at `trap`. This is the encoding `MachineL.pending_iff` uses
  internally; it is a different behaviour from the pending call.

And `tail_handler`, `tail_handler_machine`: a `return_call 0` inside the same handler (`bodyTail`)
passes it; the body ends in the **pending tail call**, the machine at `TailL`, not at a sink.
-/

namespace Silmaril.Wasm.Cfg.ExamplePending

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.MachineL Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS SCall ReachLXPS)

variable {H : Type} {s s' : Store H} {f : Frame} {a : Nat} {fi : FuncInst H}

theorem call_pending (hfi : s.func? f ⟨0⟩ = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some ([], [])) :
    ReachLXPS s f [] (liftInstrs bodyCall) [] ⟨a, ([], s)⟩ :=
  Proofs.ExamplePending.call_pending hfi hty

theorem call_pending_machine (hfi : s.func? f ⟨0⟩ = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some ([], [])) :
    ∃ (st : Machine.MState H) (l₁ l₂ : List (SCall H)),
      MRunL bodyCall (Machine.initial bodyCall s f) l₁ st ∧ ReachL bodyCall st l₂ ⟨a, ([], s)⟩ ∧
        ([] : List (SCall H)) = l₁ ++ l₂ :=
  Proofs.ExamplePending.call_pending_machine hfi hty

theorem call_throw (hfi : s.func? f ⟨0⟩ = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some ([], [])) (t : Nat) :
    EvalLXPS s f [] (liftInstrs bodyCall) [SCall.mk a [] s (.inl (.inr t)) s']
      (s', f, .flow (.brk 0 [])) :=
  Proofs.ExamplePending.call_throw hfi hty t

theorem call_throw_machine (hfi : s.func? f ⟨0⟩ = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some ([], [])) (t : Nat) :
    ∃ st : Machine.MState H, MRunL bodyCall (Machine.initial bodyCall s f)
      [SCall.mk a [] s (.inl (.inr t)) s'] st ∧ st.node.IsSink ∧
        EndRel st (s', f, .flow (.brk 0 [])) :=
  Proofs.ExamplePending.call_throw_machine hfi hty t

theorem call_trap (hfi : s.func? f ⟨0⟩ = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some ([], [])) :
    EvalLXPS s f [] (liftInstrs bodyCall) [SCall.mk a [] s (.inr ()) s'] (s', f, .flow .trap) :=
  Proofs.ExamplePending.call_trap hfi hty

theorem call_trap_machine (hfi : s.func? f ⟨0⟩ = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some ([], [])) :
    ∃ st : Machine.MState H, MRunL bodyCall (Machine.initial bodyCall s f)
      [SCall.mk a [] s (.inr ()) s'] st ∧ st.node.IsSink ∧ EndRel st (s', f, .flow .trap) :=
  Proofs.ExamplePending.call_trap_machine hfi hty

theorem tail_handler (hty : Validation.DefType.funcType? fi.type = some ([], []))
    (hfa : s.funcs[a]? = some fi) (hfi : s.func? f ⟨0⟩ = some (a, fi)) :
    EvalLXPS s f [] (liftInstrs bodyTail) [] (s, f, .tail a [] 0) :=
  Proofs.ExamplePending.tail_handler hty hfa hfi

theorem tail_handler_machine (hty : Validation.DefType.funcType? fi.type = some ([], []))
    (hfa : s.funcs[a]? = some fi) (hfi : s.func? f ⟨0⟩ = some (a, fi)) :
    ∃ (st : Machine.MState H) (l₁ l₂ : List (SCall H)),
      MRunL bodyTail (Machine.initial bodyTail s f) l₁ st ∧
        TailL bodyTail st l₂ (s, f, .tail a [] 0) :=
  Proofs.ExamplePending.tail_handler_machine hty hfa hfi

end Silmaril.Wasm.Cfg.ExamplePending
