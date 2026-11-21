module

public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Defs
import Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth

public section

namespace Silmaril.Wasm.Component.Machine

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Config (core3 grow) Host} {label : Label (core3 grow) Host}
  {trace : List (Label (core3 grow) Host)}

/-- Only the arbitrary store-update rule needs a local proof. Core instructions
may change bytes or grow memories; scheduler and trap bookkeeping keep Core intact. -/
theorem Step.core_grows (step : Step profile ready dispatch before label after)
    (updates : CoreUpdateGrows before) : Core3.Grows before.store.core after.store.core :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.step_grows step updates

theorem CoreUpdateGrows.of_inv {thread segments rest} (program : P (core3 grow) Host (Ret (core3 grow)))
    (focused : before.ctl = ⟨thread, .prog program, segments⟩ :: rest)
    (preserves : P.Inv (fun store => Core3.Grows before.store.core store.core) program) :
    CoreUpdateGrows before :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.update_of_inv program focused preserves

theorem CoreGrowthSteps.steps (run : CoreGrowthSteps profile ready dispatch before trace after) :
    Steps profile ready dispatch before trace after :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.steps run

/-- Arbitrarily many guest Core instructions supply their own growth certificate.
The Core rule cannot change the scheduler's host writer. -/
theorem CoreGrowthSteps.of_core_steps (run : Steps profile ready dispatch before trace after)
    (coreOnly : ∀ label ∈ trace, label = .core) :
    CoreGrowthSteps profile ready dispatch before trace after ∧ after.host = before.host :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.of_core_steps run coreOnly

/-- The canonical write update can change bytes, but not invalidate live memory
addresses or shrink the allocation. This is the reached update, including no-op
behavior if the low-level write cannot be performed. -/
theorem writeMemSt_grows (store : CStore (core3 grow)) (memory ptr : Nat) (bytes : ByteArray) :
    Core3.Grows store.core (writeMemSt memory ptr bytes store).core :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.writeMemSt_grows store memory ptr bytes

/-- Realloc's own dispatcher program preserves Core growth across its named
canonical updates. Late-bound callees, saved continuations and the guest Core
body run separately in the scheduler; this is deliberately a local program law. -/
theorem realloc_local_grows (ready : HostReady Host) (host : HostImpl (core3 grow) Host)
    (base : CStore (core3 grow)) (context : LiftLowerContext (core3 grow))
    (old oldLen align newLen : Nat) :
    P.Inv (fun store => Core3.Grows base.core store.core)
      (specDispatch ready host (.reallocate context old oldLen align newLen)) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.realloc_local_grows
    ready host base context old oldLen align newLen

theorem CoreGrowthSteps.grows (run : CoreGrowthSteps profile ready dispatch before trace after) :
    Core3.Grows before.store.core after.store.core :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.grows run

theorem CoreGrowthSteps.append {middle : Config (core3 grow) Host} {suffix : List (Label (core3 grow) Host)}
    (prefixSteps : CoreGrowthSteps profile ready dispatch before trace middle)
    (suffixSteps : CoreGrowthSteps profile ready dispatch middle suffix after) :
    CoreGrowthSteps profile ready dispatch before (trace ++ suffix) after :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.append prefixSteps suffixSteps

/-- The same linked memory address supplies the cached width after a certified
prefix, and an existing region still fits. No equality of guest bytes, or
validity of a pointer newly returned by realloc, follows from growth. -/
theorem CoreGrowthSteps.linked_region (run : CoreGrowthSteps profile ready dispatch before trace after)
    (context : LiftLowerContext (core3 grow)) {memory start length size : Nat} {width : AddrType}
    (linked : context.opts.memory = some memory)
    (present : (core3 grow).memAddrType? before.store.core memory = some width)
    (sized : (core3 grow).memSize? before.store.core memory = some size)
    (bounds : start + length ≤ size) :
    ptrTypeIn before.store context = width ∧ ptrTypeIn after.store context = width ∧
      ∃ reachedSize, (core3 grow).memSize? after.store.core memory = some reachedSize ∧
        size ≤ reachedSize ∧ start + length ≤ reachedSize :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.linked_region run context linked present sized bounds

/-- Resuming a saved thread or popping a continuation needs no new certificate:
the original proof covers every return value at every reached Core store. -/
theorem Step.control_growing (step : Step profile ready dispatch before label after)
    (growing : before.CoreGrowing) (install : CoreGrowthInstall dispatch before label) :
    after.CoreGrowing :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.control_growing step growing install

/-- Certify an actual run using just the initial control and the fresh programs
installed along reached prefixes. This covers returning, blocked, and trapping
runs without requiring the callback or scheduler to make progress. -/
theorem CoreGrowthSteps.of_installs (run : Steps profile ready dispatch before trace after)
    (growing : before.CoreGrowing)
    (installs : ∀ {reached next leading label}, Steps profile ready dispatch before leading reached →
      Step profile ready dispatch reached label next → CoreGrowthInstall dispatch reached label) :
    CoreGrowthSteps profile ready dispatch before trace after ∧ after.CoreGrowing :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.of_installs run growing installs

/-- Allocate, start and resolve using the actual specification dispatcher. The
synchronous lift thread and loop are included; guest callouts are separate. -/
theorem allocator_dispatch_growing (ready : HostReady Host) (host : HostImpl (core3 grow) Host)
    {call : Call (core3 grow)} (kind : AllocatorCall call) : CoreGrowing (specDispatch ready host call) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.allocator_dispatch_growing ready host kind

/-- The dispatcher keeps the entry check and confines calls in the closed
window. An unconfined import needs a certificate for its own updates. -/
theorem embedder_dispatch_growing (ready : HostReady Host) (host : HostImpl (core3 grow) Host)
    (name : String) (type : V1.FuncType) (args : List FlatValue)
    (embedder : CoreGrowing (host.embedder name type args)) :
    CoreGrowing (specDispatch ready host (.hostCallout (.embedder name type) args)) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.embedder_dispatch_growing ready host name type args embedder

/-- A separately certified callout may resume Core with new results and host
state. Its unchanged continuations retain their proofs. -/
theorem Config.CoreGrowing.replace_core_focus {thread initial reached next segments rest}
    (growing : before.CoreGrowing)
    (focused : before.ctl = ⟨thread, .core initial next, segments⟩ :: rest)
    (updatedHost : Host) :
    Config.CoreGrowing { before with
      host := updatedHost
      ctl := ⟨thread, .core reached next, segments⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth.replace_core_focus growing focused updatedHost

end Silmaril.Wasm.Component.Machine
