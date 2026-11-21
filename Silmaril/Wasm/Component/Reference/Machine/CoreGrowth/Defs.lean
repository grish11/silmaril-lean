module

public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {Host : Type}

/-- The local obligation at a reached arbitrary `modify` operation. Engine steps,
scheduler bookkeeping and traps do not need an update certificate. The dispatcher
and raw host programs may install new programs; their updates are checked when run. -/
def CoreUpdateGrows (config : Config (core3 grow) Host) : Prop :=
  match config.ctl with
  | ⟨_, .prog (.op (.modify update) _), _⟩ :: _ =>
    Core3.Grows config.store.core (update config.store).core
  | _ => True

/-- An actual scheduler prefix with evidence for just the reached `modify` operations.
This is not a restriction on guest Core memory writes, and includes trapping prefixes. -/
inductive CoreGrowthSteps (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))) :
    Config (core3 grow) Host → List (Label (core3 grow) Host) → Config (core3 grow) Host → Prop where
  | refl (config : Config (core3 grow) Host) : CoreGrowthSteps profile ready dispatch config [] config
  | cons {before current after label trace} :
    CoreUpdateGrows before → Step profile ready dispatch before label current →
    CoreGrowthSteps profile ready dispatch current trace after →
    CoreGrowthSteps profile ready dispatch before (label :: trace) after

/-- Every store update in a program preserves Core growth. Quantifying over the
base lets a saved continuation be resumed against a different reached store. -/
def CoreGrowing {Result : Type} (program : P (core3 grow) Host Result) : Prop :=
  ∀ base, P.Inv (fun store => Core3.Grows base store.core) program

/-- Proofs for every possible result are kept on pending and saved continuations. -/
def Focus.CoreGrowing : Focus (core3 grow) Host → Prop
  | .prog program => Machine.CoreGrowing program
  | .core _ next => ∀ values, Machine.CoreGrowing (next values)

def Seg.CoreGrowing : Seg (core3 grow) Host → Prop
  | .prog next => ∀ result, Machine.CoreGrowing (next result)
  | .core _ next => ∀ values, Machine.CoreGrowing (next values)

def Activation.CoreGrowing (active : Activation (core3 grow) Host) : Prop :=
  active.focus.CoreGrowing ∧ ∀ segment ∈ active.segs, Seg.CoreGrowing segment

def Config.CoreGrowing (config : Config (core3 grow) Host) : Prop :=
  (∀ active ∈ config.ctl, Activation.CoreGrowing active) ∧
    ∀ thread active, config.cont? thread = some active → Activation.CoreGrowing active

/-- Only fresh program installations need an external certificate. Built-in
host frames, resumes, and returned continuations do not install arbitrary code.
This obligation is indexed by the reached configuration, not by all possible
dispatch calls, and applies before any installed operation is executed. -/
def CoreGrowthInstall (dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow)))
    (config : Config (core3 grow) Host) (label : Label (core3 grow) Host) : Prop :=
  match label with
  | .host (.run program) => CoreGrowing program
  | .tau =>
    match config.ctl with
    | ⟨_, .prog (.op (.call call) _), _⟩ :: _ => CoreGrowing (dispatch call)
    | ⟨_, .prog (.op (.newThread body) _), _⟩ :: _ => CoreGrowing (dispatch (.threadBody body))
    | ⟨_, .core core _, _⟩ :: _ =>
      match (core3 grow).status config.store.core core with
      | .callout host args => CoreGrowing (dispatch (.hostCallout host args))
      | _ => True
    | _ => True
  | _ => True

/-- The late-bound canonical programs of the synchronous allocator protocol.
Core callouts made by the guest are not included merely because they were
reached inside realloc. They must supply their own installation certificates. -/
inductive AllocatorCall : Call (core3 grow) → Prop where
  | realloc (context : LiftLowerContext (core3 grow)) (old oldLen align newLen : Nat) :
    AllocatorCall (.reallocate context old oldLen align newLen)
  | liftThread (task : TaskId) (callee : (core3 grow).FuncAddr) :
    AllocatorCall (.threadBody (.liftImplicit task callee))
  | liftLoop (task : TaskId) : AllocatorCall (.loop (.syncLiftLoop task))
  | start (caller : CallerId) : AllocatorCall (.onStart caller)
  | resolve (caller : CallerId) (results : Option (List Value.Val)) : AllocatorCall (.onResolve caller results)

end Silmaril.Wasm.Component.Machine
