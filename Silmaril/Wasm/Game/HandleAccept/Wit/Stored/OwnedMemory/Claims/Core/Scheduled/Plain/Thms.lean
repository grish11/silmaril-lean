module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

/-- A successful body evaluation is a silent reference execution, with the actual
parked Core continuation, resumers, and saved activations left in place. -/
theorem runBody_steps {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (result : Result)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (success : runBody body start.store start.host = (updated, host, .ok result)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready dispatch start labels
        { start with store := updated, host, ctl := ⟨thread, .prog (finish result), segs⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.body_steps_at
    body start updated host result finish thread segs rest profile ready dispatch focused none (.inl rfl) success

/-- A body that reads the current thread still gives silent machine steps when
that read takes its answer from the actual activation. -/
theorem runBody_thread_steps {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (result : Result)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (success : runBody body start.store start.host (some thread) = (updated, host, .ok result)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready dispatch start labels
        { start with store := updated, host, ctl := ⟨thread, .prog (finish result), segs⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.body_steps_at
    body start updated host result finish thread segs rest profile ready dispatch focused (some thread) (.inr rfl) success

/-- A canonical trap in a non-suspending body locks down the reached store, not
the entry store. Earlier host effects survive, and no continuation is resumed.
Interpreter capability errors are not canonical traps. -/
theorem runBody_trap_steps {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (reason : TrapReason)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (failed : runBody body start.store start.host (some thread) = (updated, host, .error (.trapped reason))) :
    ∃ count, Machine.Steps profile ready dispatch start (List.replicate count .tau ++ [.trap reason])
      (Machine.StepDefs.trapCfg { start with store := updated, host }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.body_trap_steps
    body start updated host reason finish thread segs rest profile ready dispatch focused failed

/-- A resolved memory binding checks the actual caller and live `mayLeave` bit
before lifting. An ordinary refusal has the same canonical store and authority
as entry; the only effect is its typed reply in the journal. -/
theorem invoke_memory {sig : Stored.Signature} {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (host : HostState sig) (thread : Option ThreadId) :
    let binding : Binding sig := ⟨contract.name.2, contract.inst, .accept contract memory⟩
    runBody (do Scheduled.finish ticket (← Scheduled.invoke ticket binding args)) reference host (some thread) =
      match callerInstance reference thread with
      | .error issue => (reference, host, .error issue)
      | .ok caller =>
        if caller = some contract.inst ∧ (reference.inst? contract.inst).any (·.mayLeave) then
          runBody (do Scheduled.finish ticket (← Scheduled.accept ticket contract memory args)) reference host (some thread)
        else
          (reference, host.record (.refused ticket .wrongContext), .ok [i32Flat 1, i32Flat 0]) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.invoke_memory
    ticket contract memory args reference host thread

/-- The actual Core host embedder applies the memory admission rule after
recording the entry ticket. A caller refusal neither lifts nor publishes. -/
theorem embedder_memory {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩) :
    let entered := state.enter name type args
    let ticket := state.nextTicket
    runBody ((host bindings).embedder name type args) reference state (some thread) =
      match callerInstance reference thread with
      | .error issue => (reference, entered, .error issue)
      | .ok caller =>
        if caller = some contract.inst ∧ (reference.inst? contract.inst).any (·.mayLeave) then
          runBody (do Scheduled.finish ticket (← Scheduled.accept ticket contract memory args)) reference entered (some thread)
        else (reference, entered.record (.refused ticket .wrongContext), .ok [i32Flat 1, i32Flat 0]) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.embedder_memory
    bindings name type contract memory args reference state thread linked

/-- Failed binding resolution records its typed reason and traps without running
any binding body. Machine lockdown is given by `runBody_trap_steps`. -/
theorem embedder_unresolved {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (reference : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId) (issue : Issue)
    (unresolved : resolveBinding bindings name type = .error issue) :
    runBody ((host bindings).embedder name type args) reference state (some thread) =
      (reference, (state.enter name type args).record (.bindingTrap state.nextTicket issue),
        .error (.trapped (.hostTrap "invalid mixed acceptor import binding"))) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.embedder_unresolved
    bindings name type args reference state thread issue unresolved

/-- The memory accept body writes exactly the checked arena result. It records a
publication followed by a successful return, or a typed refusal without publishing. -/
theorem accept_body {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (host : HostState sig) :
    let call := Endpoints.Core.Scheduled.nodeCall contract reference args
    let attempt := Core.attempt contract memory ⟨reference, host.writer⟩ call
    let state : HostState sig := { host with writer := attempt.1.writer }
    let reply := match attempt.2 with
      | .ok handle => (state.record (.published ticket handle.toNat), completion ticket (.ok handle.toNat))
      | .error issue => (state, completion ticket (.error (.accept issue)))
    runBody (do Scheduled.finish ticket (← Scheduled.accept ticket contract memory args)) reference host =
      (attempt.1.reference, reply.1.record reply.2.1, .ok reply.2.2) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.body
    ticket contract memory args reference host

/-- Once the binding admits the caller, both memory accept paths have the same
canonical store effects, status and handle, embedded writer state and typed refusal. -/
theorem memory_plain (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (oldHost : Endpoints.Core.Scheduled.HostState sig.val)
    (journal : HostState sig.val)
    (writer : journal.writer = (Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ :
      Endpoints.Core.World grow sig.val)).writer) :
    let old := Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost reference args
    let new := runBody (do Scheduled.finish ticket (← Scheduled.accept ticket contract memory args)) reference journal
    let refused := new.2.1.newestFirst.head?.bind fun event => match event with
      | .refused _ issue => oldIssue issue
      | _ => none
    new.1 = old.1 ∧
      new.2.1.writer = (Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Endpoints.Core.World grow sig.val)).writer ∧
      new.2.2 = .ok old.2.2 ∧ old.2.1.refusals = refused.toList ++ oldHost.refusals :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.memory_plain
    sig ticket contract memory args reference oldHost journal writer

/-- A linked and admitted memory call in the actual Core embedder preserves the
plain writer embedding and the endpoint-only load's store, result and refusal.
The new journal additionally records entry and, on success, publication. -/
theorem embedder_admitted_plain (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig.val)) (name : String) (type : V1.FuncType)
    (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (oldHost : Endpoints.Core.Scheduled.HostState sig.val)
    (state : HostState sig.val) (thread : Option ThreadId)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : callerInstance reference thread = .ok (some contract.inst))
    (mayLeave : (reference.inst? contract.inst).any (·.mayLeave) = true)
    (writer : state.writer = (Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ :
      Endpoints.Core.World grow sig.val)).writer) :
    let old := Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost reference args
    let new := runBody ((host bindings).embedder name type args) reference state (some thread)
    let refused := new.2.1.newestFirst.head?.bind fun event => match event with
      | .refused _ issue => oldIssue issue
      | _ => none
    new.1 = old.1 ∧
      new.2.1.writer = (Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Endpoints.Core.World grow sig.val)).writer ∧
      new.2.2 = .ok old.2.2 ∧ old.2.1.refusals = refused.toList ++ oldHost.refusals :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.embedder_admitted_plain
    sig bindings name type contract memory args reference oldHost state thread linked caller mayLeave writer

/-- The scheduled machine reaches the actual parked Core reply for an admitted plain
memory import. Both success and a typed payload refusal advance to the same reference
store, embedded writer and status as the endpoint-only attempt. -/
theorem embedder_admitted_plain_steps (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig.val)) (name : String) (type : V1.FuncType)
    (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig.val))
    (oldHost : Endpoints.Core.Scheduled.HostState sig.val) (thread : Option ThreadId)
    (segments : List (Machine.Seg (core3 grow) (HostState sig.val)))
    (rest : List (Machine.Activation (core3 grow) (HostState sig.val)))
    (profile : ProfileKind) (ready : HostReady (HostState sig.val))
    (focused : start.ctl = ⟨thread, .prog (.flat <$> (host (grow := grow) bindings).embedder name type args),
      segments⟩ :: rest)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : callerInstance start.store thread = .ok (some contract.inst))
    (mayLeave : (start.store.inst? contract.inst).any (·.mayLeave) = true)
    (writer : start.host.writer = (Core.Plain.embedWorld sig (⟨start.store, oldHost.writer⟩ :
      Endpoints.Core.World grow sig.val)).writer) :
    let old := Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost start.store args
    ∃ (labels : List (Machine.Label (core3 grow) (HostState sig.val))) (reached : HostState sig.val),
      (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start labels
        { start with
          store := old.1
          host := reached
          ctl := ⟨thread, .prog (.pure (.flat old.2.2)), segments⟩ :: rest } ∧
      reached.writer = (Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Endpoints.Core.World grow sig.val)).writer ∧
      old.2.1.refusals = (reached.newestFirst.head?.bind fun event => match event with
        | .refused _ issue => oldIssue issue
        | _ => none).toList ++ oldHost.refusals ∧
      reached.publications = start.host.publications ++
        ((Claims.Core.attempt contract memory ⟨start.store, start.host.writer⟩
          (Endpoints.Core.Scheduled.nodeCall contract start.store args)).2.toOption.map
            fun handle => (start.host.nextTicket, handle.toNat)).toList :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.embedder_admitted_plain_steps
    sig bindings name type contract memory args start oldHost thread segments rest profile ready focused
    linked caller mayLeave writer

/-- A caller that does not satisfy the admission check gets an ordinary typed
refusal. The machine preserves the store, writer, prior publication journal and
continuation; unlike canonical lockdown, this does not prevent a later retry. -/
theorem embedder_caller_refusal_steps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (segments : List (Machine.Seg (core3 grow) (HostState sig)))
    (rest : List (Machine.Activation (core3 grow) (HostState sig)))
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (focused : start.ctl = ⟨thread, .prog (.flat <$> (host (grow := grow) bindings).embedder name type args),
      segments⟩ :: rest)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Option InstId) (resolved : callerInstance start.store thread = .ok caller)
    (refused : ¬(caller = some contract.inst ∧ (start.store.inst? contract.inst).any (·.mayLeave))) :
    let reached := (start.host.enter name type args).record (.refused start.host.nextTicket .wrongContext)
    ∃ (labels : List (Machine.Label (core3 grow) (HostState sig))),
      (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start labels
        { start with
          host := reached
          ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } ∧
      reached.writer = start.host.writer ∧ reached.publications = start.host.publications :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.embedder_caller_refusal_steps
    bindings name type contract memory args start thread segments rest profile ready focused linked caller resolved refused

/-- Binding failures in the actual scheduler retain their typed diagnostic in
the journal and take the reference lockdown transition, rather than replying
with an ordinary call-local status. -/
theorem embedder_binding_trap_steps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (segments : List (Machine.Seg (core3 grow) (HostState sig)))
    (rest : List (Machine.Activation (core3 grow) (HostState sig)))
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (issue : Issue)
    (focused : start.ctl = ⟨thread, .prog (.flat <$> (host (grow := grow) bindings).embedder name type args),
      segments⟩ :: rest)
    (unresolved : resolveBinding bindings name type = .error issue) :
    let reached := (start.host.enter name type args).record (.bindingTrap start.host.nextTicket issue)
    let reason := TrapReason.hostTrap "invalid mixed acceptor import binding"
    ∃ count, Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start
      (List.replicate count .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg { start with host := reached }) :=
  runBody_trap_steps _ start start.store _ _ (fun words => .pure (.flat words)) thread segments rest
    profile ready _ focused (embedder_unresolved bindings name type args start.store start.host thread issue unresolved)

/-- Enter the actual dispatched embedder callout from parked Core. The prefix
reads the caller and store and leaves the confinement choice to `calloutBody`. -/
theorem prepend_embedder_callout {E : CoreEngine} {Host : Type}
    [∀ left right, Decidable (E.ExternSub left right)]
    {ready : HostReady Host} {impl : HostImpl E Host} {profile : ProfileKind}
    {start final : Machine.Config E Host} {thread continuation}
    {core : E.Thread (CanonHost E)} {segments rest name type args labels}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : E.status start.store.core core = .callout (.embedder name type) args)
    (tail : Machine.Steps profile ready (specDispatch ready impl)
      { start with ctl := ⟨thread, .prog (calloutBody Limits.spec Quirks.none ready impl
          start.store thread (.embedder name type) args),
        .core core continuation :: segments⟩ :: rest } labels final) :
    Machine.Steps profile ready (specDispatch ready impl) start (.tau :: .tau :: .tau :: labels) final :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.prepend_embedder_callout
    parked calling tail

/-- A parked Core call to an admitted plain memory import runs the checked
host and resumes at the reached Core store with the endpoint-only status.
The journal adds exactly one ticketed publication on success and none on
refusal. On a checked configuration the successful handle selects the new
root immediately. This does not cover the caller's remaining instructions. -/
theorem parked_admitted_plain_steps (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig.val)) (name : String) (type : V1.FuncType)
    (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig.val))
    (oldHost : Endpoints.Core.Scheduled.HostState sig.val) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig.val))
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : callerInstance start.store thread = .ok (some contract.inst))
    (mayLeave : (start.store.inst? contract.inst).any (·.mayLeave) = true)
    (writer : start.host.writer = (Core.Plain.embedWorld sig (⟨start.store, oldHost.writer⟩ :
      Endpoints.Core.World grow sig.val)).writer) :
    let old := Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost start.store args
    let attempt := Claims.Core.attempt contract memory ⟨start.store, start.host.writer⟩
      (Endpoints.Core.Scheduled.nodeCall contract start.store args)
    ∃ (labels : List (Machine.Label (core3 grow) (HostState sig.val))) (reached : HostState sig.val),
      (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start labels
        { start with
          store := old.1
          host := reached
          ctl := ⟨thread, .core ((core3 grow).resume old.1.core core (.values old.2.2)) continuation,
            segments⟩ :: rest } ∧
      reached.writer = (Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Endpoints.Core.World grow sig.val)).writer ∧
      old.2.1.refusals = (reached.newestFirst.head?.bind fun event => match event with
        | .refused _ issue => oldIssue issue
        | _ => none).toList ++ oldHost.refusals ∧
      reached.publications = start.host.publications ++
        (attempt.2.toOption.map fun handle => (start.host.nextTicket, handle.toNat)).toList ∧
      ∀ handle, attempt.2 = .ok handle → Machine.CfgSafe CheckedWrite start →
        ∃ tree, reached.writer.accepted = tree :: start.host.writer.accepted ∧
          Endpoints.Core.childFromHistory reached.writer.accepted handle = some tree :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.parked_admitted_plain_steps
    sig bindings name type contract memory args start oldHost thread profile ready parked calling
    linked caller mayLeave writer

/-- Binding failure preserves the typed diagnostic and reaches canonical
lockdown from parked Core, even when the embedder is confined. -/
theorem parked_binding_trap_steps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (issue : Issue)
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (unresolved : resolveBinding bindings name type = .error issue) :
    let reached := (start.host.enter name type args).record (.bindingTrap start.host.nextTicket issue)
    let reason := TrapReason.hostTrap "invalid mixed acceptor import binding"
    ∃ count, Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start
      (List.replicate count .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg { start with host := reached }) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.parked_binding_trap_steps
    bindings name type args start thread profile ready issue parked calling unresolved

/-- Refusal of a resolved memory binding is call-local in both dispatcher
branches, including when the current instance may not leave. Core resumes
with the error status; the store, writer and prior publications are unchanged. -/
theorem parked_caller_refusal_steps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Option InstId) (resolved : callerInstance start.store thread = .ok caller)
    (refused : ¬(caller = some contract.inst ∧ (start.store.inst? contract.inst).any (·.mayLeave))) :
    let reached := (start.host.enter name type args).record (.refused start.host.nextTicket .wrongContext)
    ∃ (labels : List (Machine.Label (core3 grow) (HostState sig))),
      (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start labels
        { start with
          host := reached
          ctl := ⟨thread, .core ((core3 grow).resume start.store.core core (.values [i32Flat 1, i32Flat 0]))
            continuation, segments⟩ :: rest } ∧
      reached.writer = start.host.writer ∧ reached.publications = start.host.publications :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled.parked_caller_refusal_steps
    bindings name type contract memory args start thread profile ready parked calling linked caller resolved refused

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain
