module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Defs
import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Simulation

public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {context : Context} {world : World H context}
  {locals input middle results : List IntType} {profile : Profile} {host : HostSemantics H}

theorem Code.erase_append (left : Code locals input middle) (right : Code locals middle results) :
    (left.append right).erase = left.erase ++ right.erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.append_erase left right

theorem Code.sound (code : Code locals input results) (h : context.locals = localTypes locals) :
    InstrsOk context code.erase (.plain (stackTypes input) (stackTypes results)) :=
  Proofs.Wasm.Execution.Core.Intrinsic.code_ok code h

theorem LocalFrame.sound (frame : LocalFrame world locals) :
    FrameOk world.store frame.erase {context with locals := localTypes locals} :=
  Proofs.Wasm.Execution.Core.Intrinsic.frame_ok frame

theorem State.sound (state : State world locals results) :
    ConfigOk state.erase (stackTypes results) :=
  Proofs.Wasm.Execution.Core.Intrinsic.state_ok state

/-- Every executable typed transition is exactly one Core step, for any
numeric profile and host relation. No raw preservation theorem is needed. -/
theorem State.step_sound {state next : State world locals results} (h : state.step? = some next) :
    Step profile host state.erase next.erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.step_sound h

/-- In a host-free deterministic profile, a raw step out of an active
configuration has exactly the typed successor. In particular, a values-only
configuration has no such step. -/
theorem State.run_reflect {oracle : GrowKind → Nat → Nat → Nat → Bool}
    (frame : LocalFrame world locals) (stack : Values input) (code : Code locals input results)
    {target : Config H}
    (step : Step (Profile.deterministic oracle) (fun _ _ _ _ => False)
      (State.mk frame (.run stack code)).erase target) :
    ∃ next : State world locals results,
      (State.mk frame (.run stack code)).step? = some next ∧ target = next.erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.run_reflect frame stack code step

/-- Reflection including trap propagation. A raw step can propagate a trap
only partway; its target then reaches the typed target by one further step. -/
theorem State.step_reflect {oracle : GrowKind → Nat → Nat → Nat → Bool}
    {state : State world locals results} {target : Config H}
    (step : Step (Profile.deterministic oracle) (fun _ _ _ _ => False) state.erase target) :
    ∃ next, state.step? = some next ∧ Relation.ReflGen
      (Step (Profile.deterministic oracle) (fun _ _ _ _ => False)) target next.erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.step_reflect step

theorem State.result_sound {state : State world locals results} {result : Result}
    (h : state.result? = some result) : state.erase.code = result.toAdmin ∧
      ∀ target, ¬ Step profile (fun _ _ _ _ => False) state.erase target :=
  Proofs.Wasm.Execution.Core.Intrinsic.result_sound h

theorem State.runFor_sound (fuel : Nat) (state : State world locals results) :
    Steps profile host state.erase (state.runFor fuel).erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.runFor_sound fuel state

end Silmaril.Wasm.Execution.Core.Intrinsic
