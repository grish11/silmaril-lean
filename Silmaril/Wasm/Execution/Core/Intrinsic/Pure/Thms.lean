module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Pure.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Thms
import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Pure

public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic.Pure

open Numerics SingleThreaded SingleThreaded.Det

variable {locals input middle output : List IntType}

theorem eval_append (frame : Values locals) (left : Code locals input middle)
    (right : Code locals middle output) (stack : Values input) :
    eval frame (left.append right) stack = (eval frame left stack).bind (eval frame right) :=
  Proofs.Wasm.Execution.Core.Intrinsic.Pure.eval_append frame left right stack

theorem run_eval {H : Type} {context : Validation.Context} {world : World H context}
    (frame : LocalFrame world locals) (code : Code locals input output) (stack : Values input) :
    ((State.mk frame (.run stack code)).runFor (budget code)).control.result? =
      some (eval frame.values code stack) :=
  Proofs.Wasm.Execution.Core.Intrinsic.Pure.run_eval frame code stack

theorem invoke_denotes {H : Type} {context : Validation.Context} {world : World H context}
    {parameters results : List IntType} (call : DirectCall world parameters results)
    (args : Values parameters) (oracle : GrowOracle) :
    behaviours (profile oracle) noHost world.store call.address args.erase =
      {(invokeResult (denotes call.body args)).toBehaviour} :=
  Proofs.Wasm.Execution.Core.Intrinsic.Pure.invoke_denotes call args oracle

theorem Linked.observation {parameters declared results : List IntType}
    {body : Code (parameters ++ declared) [] results} (entry : Linked body)
    (args : Values parameters) (oracle : GrowOracle) :
    behaviours (profile oracle) noHost entry.world.store entry.call.address args.erase =
      {(invokeResult (denotes body args)).toBehaviour} :=
  Proofs.Wasm.Execution.Core.Intrinsic.Pure.linked_observation entry args oracle

/-- Full abstraction for the specified linked numeric suffix contexts.
The base links witness that the identity test is available. The right-hand
side is equality of store-free, typed denotations, not an observation clause. -/
theorem postEquivalent_iff {parameters declared results : List IntType}
    {first second : Code (parameters ++ declared) [] results}
    (firstEntry : Linked first) (secondEntry : Linked second) (oracle : GrowOracle) :
    PostEquivalent first second ↔ ∀ args, denotes first args = denotes second args :=
  Proofs.Wasm.Execution.Core.Intrinsic.Pure.postEquivalent_iff firstEntry secondEntry oracle

end Silmaril.Wasm.Execution.Core.Intrinsic.Pure
