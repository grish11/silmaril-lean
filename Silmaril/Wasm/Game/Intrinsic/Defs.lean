module

public import Silmaril.Wasm.Game.DivAdequacy.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Defs
public import Silmaril.Games.DivComp.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.Intrinsic

open Silmaril.Games Execution.Core Numerics
open Validation (CModuleType Context DefType)

/-- A scalar view of an already instantiated intrinsic module. This does not run
instantiation. In addition to `IsInstance`, the export correspondence excludes
unrepresented non-function exports and identifies the actual interface types. -/
structure Registered {interface : CModuleType} (program : Validation.Intrinsic.Module interface) where
  instance_ : ScalarInstance
  ready : IsInstance program.erase interface instance_
  exports : List.Forall₂ (fun external sig => ∃ type, external = .func type ∧
    FnType.ofDefType? type = some sig) interface.exports instance_.exports

/-- The open, divergence-observing strategy of a registered intrinsic module. -/
noncomputable def Registered.denote {interface} {program : Validation.Intrinsic.Module interface}
    (registered : Registered program) (profile : Profile) :
    DStrategy registered.instance_.E registered.instance_.F :=
  registered.instance_.dstrategy profile registered.instance_.store

/-- A particular instance export is implemented by this intrinsic function's
erasure, not merely by another function of the same signature. The store and
resolved address are explicit; the address and code cannot be chosen separately. -/
structure Entry {context : Context} {type : DefType}
    (func : Validation.Intrinsic.Function context type) (instance_ : ScalarInstance)
    (store : Store Nat) (sig : FnType) where
  slot : Fin instance_.exports.length
  signature : instance_.exports.get slot = sig
  scalar : FnType.ofDefType? type = some sig
  address : Nat
  resolved : instance_.addr slot = address
  implementation : ModuleInst
  code : store.funcs[address]? = some ⟨type, implementation, .wasm func.erase⟩

namespace Entry

variable {context : Context} {type : DefType} {func : Validation.Intrinsic.Function context type}
  {I : ScalarInstance} {store : Store Nat} {sig : FnType}

/-- The typed application supplies the question to the existing instance game. -/
def question (entry : Entry func I store sig) (args : Typed sig.params) : I.F.Op :=
  ⟨entry.slot, entry.signature.symm ▸ args⟩

/-- One complete open application. Import questions/answers stay visible and
the target store (also after a trap) is retained. A non-finishing application
is not encoded as an empty round; use the enclosing `DStrategy` for divergence. -/
def round (entry : Entry func I store sig) (profile : Profile) (args : Typed sig.params)
    (moves : List (Move I.E I.F)) (target : Store Nat) : Prop :=
  I.Path profile (.running (entry.question args) store (I.initThread (entry.question args)))
    moves (.idle target) ∧ ∀ op, .inr (.ask op) ∉ moves

/-- Close the instance strategy by composing with a game-definable host, then
observe this application's question (including may-divergence). -/
noncomputable def denote (entry : Entry func I store sig) (profile : Profile)
    (env : Env I.E) (args : Typed sig.params) : Set (Behaviour Val) :=
  dcompositeObs (env.dstrategy.comp (I.dstrategy profile store)) (entry.question args)

end Entry

end Silmaril.Wasm.Game.Intrinsic
