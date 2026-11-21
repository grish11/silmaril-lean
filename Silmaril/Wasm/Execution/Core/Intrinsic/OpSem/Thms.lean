module

public import Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Defs
public import Silmaril.Semantics.Operational.Policy.Thms
import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.OpSem

public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Numerics Validation SingleThreaded Semantics.Operational

variable {H : Type} {context : Context} {world : World H context}
  {locals results : List IntType} {oracle : GrowOracle}

theorem State.typedReach_iff (state target : State world locals results) :
    typedSem.toOpSem.Reach state target ↔ ∃ fuel, state.runFor fuel = target :=
  Proofs.Wasm.Execution.Core.Intrinsic.OpSem.typedReach_iff state target

theorem State.raw_safe (state : State world locals results) :
    (rawSem oracle (stackTypes results)).SafeAt state.erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.OpSem.raw_safe state

/-- On an erased intrinsic state, the typed machine and policy-gated Core
have exactly the same finite return and trap observations. -/
theorem State.may_iff (state : State world locals results) (outcome : Outcome Completion) :
    (rawSem oracle (stackTypes results)).toOpSem.May state.erase outcome ↔ typedSem.toOpSem.May state outcome :=
  Proofs.Wasm.Execution.Core.Intrinsic.OpSem.may_iff state outcome

theorem State.typed_deterministic (state : State world locals results) : typedSem.toOpSem.DetFrom state :=
  Proofs.Wasm.Execution.Core.Intrinsic.OpSem.typed_deterministic state

end Silmaril.Wasm.Execution.Core.Intrinsic
