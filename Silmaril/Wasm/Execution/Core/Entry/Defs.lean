module

public import Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs
public import Silmaril.Wasm.Abstract.InstSession.Defs

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Entry

open Validation Numerics SingleThreaded Semantics.Operational Game
open Intrinsic (Completion observeResult DirectCall Values World State typedSem)

variable {H : Type}

def ordinary (P : Profile) (host : HostSemantics H) : OpSem (Config H) Completion where
  step := Step P host
  observe state outcome := ∃ result : Result, state.code = result.toAdmin ∧ observeResult result = outcome

def policy (P : Profile) (host : HostSemantics H) (results : List CValType) : WithUB (Config H) Completion :=
  (.ofOpSem (ordinary P host) : WithUB (Config H) Completion).enforce (fun state => ConfigOk state results)

/-- The store-bearing version of a finite observation, including traps and throws. -/
def Finishes (P : Profile) (host : HostSemantics H) (source final : Config H) (result : Result) : Prop :=
  Steps P host source final ∧ final.code = result.toAdmin

/-- Core instantiation receives externally resolved addresses in import order.
Failure of resolution is not a trap or a UB state in this machine. -/
structure ModuleInput (H : Type) where
  store : Store H
  module_ : Wasm.Module
  imports : List ExternAddr

def rawModule (P : Profile) (host : HostSemantics H) : HasOpSem (ModuleInput H) (Config H) Completion where
  initial input state := Instantiate P host input.store input.module_ input.imports state
  semantics := policy P host []

structure TypedModuleInput (H : Type) (interface : CModuleType) where
  store : Store H
  module_ : Validation.Intrinsic.Module interface
  imports : List ExternAddr
  storeOk : StoreOk store
  importsOk : List.Forall₂ (ExternAddrOk store) imports interface.imports

def TypedModuleInput.erase {interface : CModuleType} (input : TypedModuleInput H interface) : ModuleInput H :=
  ⟨input.store, input.module_.erase, input.imports⟩

/-- Same Core start/segment rules on configurations with an actual typing proof.
This is typed module entry, not a new intrinsic evaluator for start code. -/
def typedModule (P : Profile) (host : HostSemantics H) (interface : CModuleType) :
    HasOpSem (TypedModuleInput H interface) { state : Config H // ConfigOk state [] } Completion where
  initial input state := (rawModule P host).initial input.erase state.val
  semantics := (policy P host []).restrict (fun state => ConfigOk state [])

structure Ready (H : Type) where
  store : Store H
  instance_ : ModuleInst

/-- A ready instance consists of the allocated module and the store *after*
segments and start. Neither a trap nor an exception publishes a ready instance. -/
def ReadyAfter (P : Profile) (host : HostSemantics H) (input : ModuleInput H) (ready : Ready H) : Prop :=
  ∃ source final, (rawModule P host).initial input source ∧
    Finishes P host source final (.values []) ∧ ready = ⟨final.store, source.frame.module⟩

structure ExportInput (H : Type) where
  ready : Ready H
  name : String
  args : List Val

/-- Name lookup is an entry premise. This raw entry does not validate arguments:
that is separate from lookup, and the policy uses `ConfigOk` at the given results. -/
def rawExport (P : Profile) (host : HostSemantics H) (results : List CValType) :
    HasOpSem (ExportInput H) (Config H) Completion where
  initial input state := ∃ address, Accept.exportFunc? input.ready.instance_ input.name = some address ∧
    state = invoke input.ready.store address input.args
  semantics := policy P host results

variable {context : Context} {world : World H context} {parameters results : List IntType}

/-- A named function in the caller's ready module, with a checked resolved body. -/
structure ResolvedExport (call : DirectCall world parameters results) where
  name : String
  lookup : Accept.exportFunc? world.moduleInst name = some call.address

def ResolvedExport.rawInput {call : DirectCall world parameters results} (entry : ResolvedExport call)
    (args : Values parameters) : ExportInput H :=
  ⟨⟨world.store, world.moduleInst⟩, entry.name, args.erase⟩

/-- Argument-indexed entry for the resolved named export. The machine is the
existing intrinsic function body, not the raw invoke wrapper. -/
def ResolvedExport.opSem {call : DirectCall world parameters results} (_entry : ResolvedExport call) :=
  call.opSem

/-- Ready scalar-instance entry at a supplied current store, not reinstantiation.
The ordinary transitions are the host-free phase of an activation. Consumers
needing host answers must use the session, not infer UB from a missing step. -/
def scalarInstance (oracle : GrowOracle) (instance_ : ScalarInstance) (results : List CValType) :
    HasOpSem (Store Nat × instance_.F.Op) (Config Nat) Completion where
  initial input state := state = (instance_.initThread input.2).config input.1
  semantics := policy (profile oracle) Det.noHost results

/-- A typed activation of a selected intrinsic body at the current instance store.
Only questions whose address and arguments match that body are admitted. -/
def typedInstance {readyWorld : World Nat context} (instance_ : ScalarInstance)
    (call : DirectCall readyWorld parameters results) (_wellFormed : instance_.WellFormed readyWorld.store) :
    HasOpSem instance_.F.Op (State call.world (parameters ++ call.declaredLocals) results) Completion where
  initial question state := ∃ args : Values parameters, instance_.addr question.1 = call.address ∧
    question.2.val = args.erase ∧ state = call.start args
  semantics := typedSem

end Silmaril.Wasm.Execution.Core.Entry
