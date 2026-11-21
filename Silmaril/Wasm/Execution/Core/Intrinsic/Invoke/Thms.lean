module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Defs
public import Silmaril.Wasm.SingleThreaded.Profile
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Invoke

public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Numerics SingleThreaded SingleThreaded.Det

variable {H : Type} {leftCtx rightCtx : Validation.Context} {left : World H leftCtx}
  {right : World H rightCtx} {parameters results : List IntType} {oracle : GrowOracle}

/-- Typed integer arguments cover all arguments accepted by the resolved raw address. -/
theorem DirectCall.invokeOk_iff (call : DirectCall left parameters results) (vs : List Val) :
    InvokeOk left.store call.address vs ↔ ∃ args : Values parameters, args.erase = vs :=
  Proofs.Wasm.Execution.Core.Intrinsic.Invoke.invokeOk_iff call vs

/-- A finite typed answer rules out divergence even along alternative raw trap-bubbling paths. -/
theorem DirectCall.invoke_not_diverges (call : DirectCall left parameters results) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (returned : call.runFor args fuel = some answer) :
    ¬ Diverges (profile oracle) noHost (invoke left.store call.address args.erase) :=
  Proofs.Wasm.Execution.Core.Intrinsic.Invoke.invoke_not_diverges call args returned

/-- A finite typed answer determines the entire behaviour set. Fuel exhaustion
is not an answer and gives no such guarantee. -/
theorem DirectCall.invoke_behaviours (call : DirectCall left parameters results) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (returned : call.runFor args fuel = some answer) :
    behaviours (profile oracle) noHost left.store call.address args.erase = {(invokeResult answer).toBehaviour} :=
  Proofs.Wasm.Execution.Core.Intrinsic.Invoke.invoke_behaviours call args returned

/-- Exact equality of observations, including divergence, for a pair of successful typed runs. -/
theorem DirectCall.invocations_eq_iff (first : DirectCall left parameters results)
    (second : DirectCall right parameters results) (args : Values parameters)
    {firstFuel secondFuel : Nat} {firstAnswer secondAnswer : Option (Values results)}
    (firstRun : first.runFor args firstFuel = some firstAnswer)
    (secondRun : second.runFor args secondFuel = some secondAnswer) :
    behaviours (profile oracle) noHost left.store first.address args.erase =
        behaviours (profile oracle) noHost right.store second.address args.erase ↔
      (invokeResult firstAnswer).toBehaviour = (invokeResult secondAnswer).toBehaviour :=
  Proofs.Wasm.Execution.Core.Intrinsic.Invoke.invocations_eq_iff first second args firstRun secondRun

theorem DirectCall.entry_eq (first : DirectCall left parameters results) (second : DirectCall right parameters results)
    (runs : ∀ args, ∃ firstFuel secondFuel answer,
      first.runFor args firstFuel = some answer ∧ second.runFor args secondFuel = some answer) :
    EntryAgreement Eq (profile oracle) noHost left.store right.store first.address second.address :=
  Proofs.Wasm.Execution.Core.Intrinsic.Invoke.entry_eq first second runs

variable {R : Behaviour Val → Behaviour Val → Prop} {P : Profile} {host : HostSemantics H}
  {s t : Store H} {first second : Nat}

theorem EntryAgreement.funEquiv (agreement : EntryAgreement R P host s s first second) :
    FunEquiv R P host s first second :=
  ⟨fun vs h => (agreement.observes vs h).1, fun vs h => (agreement.observes vs ((agreement.accepts vs).mpr h)).2⟩

/-- Cover each accepted address in either store, not just the exported subset.
This is closed-store comparison, not contextual substitution. -/
theorem EntryAgreement.moduleEquiv
    (cover : ∀ address, (∃ vs, InvokeOk s address vs ∨ InvokeOk t address vs) →
      EntryAgreement R P host s t address address) : ModuleEquiv R P host s t :=
  ⟨fun address vs h => ((cover address ⟨vs, .inl h⟩).observes vs h).1,
    fun address vs h => let entry := cover address ⟨vs, .inr h⟩
                        (entry.observes vs ((entry.accepts vs).mpr h)).2⟩

end Silmaril.Wasm.Execution.Core.Intrinsic
