module

public import Silmaril.Wasm.Execution.Core.Entry.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Defs
import Silmaril.Proofs.Wasm.Execution.Core.Entry

public section

namespace Silmaril.Wasm.Execution.Core.Entry

open Validation Numerics SingleThreaded SingleThreaded.Det Semantics.Operational Game
open Intrinsic (Completion observeResult DirectCall Values World stackTypes invokeResult)
open Silmaril.Games.Abstract Silmaril.Wasm.Abstract.InstSession

variable {H : Type} {P : Profile} {host : HostSemantics H} {types : List CValType}

theorem ordinary_may {source : Config H} {outcome : Outcome Completion} :
    (ordinary P host).May source outcome ↔ ∃ final result, Finishes P host source final result ∧
      observeResult result = outcome :=
  Proofs.Wasm.Execution.Core.Entry.ordinary_may

/-- Raw administrative steps need not be unique, but any two finished
executions at the deterministic profile agree on the entire final state. -/
theorem finishes_unique {oracle : GrowOracle} {source first second : Config H} {one two : Result}
    (left : Finishes (profile oracle) noHost source first one)
    (right : Finishes (profile oracle) noHost source second two) : first = second ∧ one = two :=
  Proofs.Wasm.Execution.Core.Entry.finishes_unique left right

/-- A preserved typing policy adds neither UB nor losses of ordinary observations from a typed source. -/
theorem policy_safe_and_may {source : Config H}
    (preserves : ∀ ⦃left right : Config H⦄, ConfigOk left types → Step P host left right → ConfigOk right types)
    (typed : ConfigOk source types) :
    (policy P host types).SafeAt source ∧
      ∀ outcome, (policy P host types).toOpSem.May source outcome ↔ (ordinary P host).May source outcome :=
  Proofs.Wasm.Execution.Core.Entry.policy_safe_and_may preserves typed

/-- Host-free preservation alone does not give progress through an unanswered callout. -/
theorem noHost_preserves {left right : Config H} (typed : ConfigOk left types) (step : Step P noHost left right) :
    ConfigOk right types :=
  Proofs.Wasm.Execution.Core.Entry.noHost_preserves typed step

/-- Lifts an actual instantiation against the provided resolved imports; not an existence theorem. -/
theorem typedModule_lift {interface : CModuleType} {input : TypedModuleInput H interface} {source : Config H}
    (hostOk : HostOk host) : (rawModule P host).initial input.erase source ↔
      ∃ state, (typedModule P host interface).initial input state ∧ state.val = source :=
  Proofs.Wasm.Execution.Core.Entry.typedModule_lift hostOk

theorem typedModule_noUB {interface : CModuleType} (source : { state : Config H // ConfigOk state [] }) :
    ((typedModule P host interface).semantics).SafeAt source :=
  fun ⟨target, _, bad⟩ => bad.elim False.elim fun notTyped => notTyped target.property

/-- With a type-preserving host, restricting to typed configurations loses no finite Core outcomes. -/
theorem typedModule_may {interface : CModuleType} (hostOk : HostOk host)
    (source : { state : Config H // ConfigOk state [] }) (outcome : Outcome Completion) :
    (typedModule P host interface).semantics.toOpSem.May source outcome ↔
      ∃ final result, Finishes P host source.val final result ∧ observeResult result = outcome :=
  Proofs.Wasm.Execution.Core.Entry.typedModule_may hostOk source outcome

variable {context : Context} {world : World H context} {parameters results : List IntType}
  {call : DirectCall world parameters results} {oracle : GrowOracle}

theorem ResolvedExport.raw_initial_iff (entry : ResolvedExport call) (args : Values parameters) (state : Config H) :
    (rawExport P host types).initial (entry.rawInput args) state ↔
      state = invoke world.store call.address args.erase :=
  ⟨fun ⟨_, found, initial⟩ => (Option.some.inj (entry.lookup.symm.trans found)).symm ▸ initial,
    fun initial => ⟨_, entry.lookup, initial⟩⟩

theorem invoke_typed (call : DirectCall world parameters results) (args : Values parameters) :
    ConfigOk (invoke world.store call.address args.erase) (stackTypes results) :=
  Proofs.Wasm.Execution.Core.Entry.invoke_typed call args

theorem invoke_noUB (call : DirectCall world parameters results) (args : Values parameters) :
    (policy (profile oracle) noHost (stackTypes results)).SafeAt (invoke world.store call.address args.erase) :=
  (policy_safe_and_may (fun {_ _} => noHost_preserves) (invoke_typed call args)).1

/-- A finite typed answer pins the actual Core result, frame and store, including on a trap. -/
theorem invoke_finishes_iff (call : DirectCall world parameters results) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    {final : Config H} {result : Result} :
    Finishes (profile oracle) noHost (invoke world.store call.address args.erase) final result ↔
      final = ⟨world.store, {}, (invokeResult answer).toAdmin⟩ ∧ result = invokeResult answer :=
  Proofs.Wasm.Execution.Core.Entry.invoke_finishes_iff call args ran

theorem invoke_may_iff (call : DirectCall world parameters results) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    (outcome : Outcome Completion) :
    (policy (profile oracle) noHost (stackTypes results)).toOpSem.May
      (invoke world.store call.address args.erase) outcome ↔ outcome = observeResult (invokeResult answer) :=
  Proofs.Wasm.Execution.Core.Entry.invoke_may_iff call args ran outcome

/-- Compares the typed body machine with actual named raw entry, including Core invoke wrappers.
The finite-answer premise is not a test for divergence. -/
theorem ResolvedExport.may_iff (entry : ResolvedExport call) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    (outcome : Outcome Completion) :
    (entry.opSem.semantics.toOpSem.May (call.start args) outcome) ↔
      (rawExport (profile oracle) noHost (stackTypes results)).semantics.toOpSem.May
        (invoke world.store call.address args.erase) outcome :=
  Proofs.Wasm.Execution.Core.Entry.typed_invoke_may_iff args ran outcome

/-- Agreement for an admitted typed instance question and the corresponding raw activation. -/
theorem typedInstance_may_iff {registered : ScalarInstance} {readyWorld : World Nat context}
    (call : DirectCall readyWorld parameters results) (wellFormed : registered.WellFormed readyWorld.store)
    (args : Values parameters) (question : registered.F.Op)
    (address : registered.addr question.1 = call.address) (arguments : question.2.val = args.erase)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    (outcome : Outcome Completion) :
    (typedInstance registered call wellFormed).semantics.toOpSem.May (call.start args) outcome ↔
      (scalarInstance oracle registered (stackTypes results)).semantics.toOpSem.May
        ((registered.initThread question).config readyWorld.store) outcome :=
  Proofs.Wasm.Execution.Core.Entry.typedInstance_may_iff call wellFormed args question address arguments ran outcome

/-- Exact one-activation readback for a selected typed export of an import-free registration.
Uses the real session observer, not a component evaluator. Address, arguments and answer typing
must agree with the registration at the current store. `ran` is required even to rule out divergence. -/
theorem session_finishes_iff {registered : ScalarInstance} {readyWorld : World Nat context}
    (call : DirectCall readyWorld parameters results)
    (args : Values parameters) {question : registered.F.Op} (closed : registered.imports = [])
    (address : registered.addr question.1 = call.address) (arguments : question.2.val = args.erase)
    {fuel : Nat} {answer : Option (Values results)} (ran : call.runFor args fuel = some answer)
    {typedAnswer : registered.F.Ar question}
    (readback : Answer.ofResult? (registered.exports.get question.1) (invokeResult answer) = some typedAnswer)
    (log : List (Call registered.E)) (ending : End (Store Nat) (Res registered.exports ⊕ PUnit)) :
    (log, ending) ∈ instFinS registered (profile oracle) readyWorld.store question ↔
      ending = .ret (sAns question typedAnswer) readyWorld.store :=
  Proofs.Wasm.Execution.Core.Entry.session_finishes_iff call args closed address arguments ran readback log ending

end Silmaril.Wasm.Execution.Core.Entry
