module

public import Silmaril.Semantics.Operational.Policy.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Defs
public import Silmaril.Wasm.SingleThreaded.Profile

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Numerics Validation SingleThreaded Semantics.Operational

/-- A non-trap completion can carry an uncaught exception. Only `.ok` is
successful return; `.error` is neither a success nor a trap. -/
abbrev Completion := Except Nat (List Val)

def observeResult : Result → Outcome Completion
  | .values values => .returned (.ok values)
  | .throw addr => .returned (.error addr)
  | .trap => .trap

def rawOrdinary {H : Type} (oracle : GrowOracle) : OpSem (Config H) Completion where
  step := Step (profile oracle) (fun _ _ _ _ => False)
  observe state outcome := ∃ result : Result, state.code = result.toAdmin ∧ observeResult result = outcome

/-- On bad configurations the policy reports UB instead of allowing steps or
observations. At a good configuration these are the actual Core relations. -/
def rawSem {H : Type} (oracle : GrowOracle) (types : List CValType) : WithUB (Config H) Completion :=
  (WithUB.ofOpSem (rawOrdinary oracle)).enforce (fun state => ConfigOk state types)

variable {H : Type} {context : Context} {world : World H context}
  {locals parameters results : List IntType}

/-- The execution rules come from intrinsic `step?`, not a pullback of Core. -/
def typedSem : WithUB (State world locals results) Completion :=
  .ofOpSem {
    step := fun source target => source.step? = some target
    observe := fun state outcome => ∃ result, state.result? = some result ∧ observeResult result = outcome }

/-- Function-body entry once a direct call has been resolved. The landed
`DirectCall.invoke_behaviours` theorem separately handles raw invoke wrappers. -/
def DirectCall.opSem (call : DirectCall world parameters results) :
    HasOpSem (Values parameters) (State call.world (parameters ++ call.declaredLocals) results) Completion where
  initial args state := state = call.start args
  semantics := typedSem

end Silmaril.Wasm.Execution.Core.Intrinsic
