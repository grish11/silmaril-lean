module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

/-- A raw host assignment is not a closed guest step. In particular, the
absence of a host read does not rule out an assignment installed by an open hook. -/
def NoHostAssignment (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ thread value next frames rest,
    state.ctl ≠ ⟨thread, .prog (.op (.hostSet value) next), frames⟩ :: rest

/-- Reached allocator steps before a protected return. Ordinary steps must
not install an overlaid give or assign the host; confined gives and
reached host reads with a closed observation have their own rules. The endpoint may
be suspended, trapped, ready to pop a protected frame, or at an open hook. -/
inductive ClosedCallbackPrefix (bindings : List (Binding sig)) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (base : HostImpl (core3 grow) (HostState sig))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop) :
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | done (state : Config (core3 grow) (HostState sig)) : ClosedCallbackPrefix bindings profile ready base protectedReturn state [] state
  | step {start next finish label seen}
      (interior : HostFrame.InteriorFor protectedReturn start) (unchanged : UnchangedAt bindings start)
      (noAssignment : NoHostAssignment start) (grows : CoreUpdateGrows start)
      (run : Step profile ready (specDispatch ready base) start label next)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn next seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start (PayloadPrefix.visible [label] ++ seen) finish
  | confinedGive {start finish seen} (callout : LinkedCallback.ClosedGive bindings start)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn callout.resume seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish
  | closedRead {start finish seen thread frames rest resume}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
      (agrees : ∀ host, resume start.host = resume host)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn { start with ctl := ⟨thread,
        .prog (resume start.host), frames⟩ :: rest } seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish

/-- A reached synchronous lift read whose candidate filter is independent
of the embedder host at the consulted queries. -/
def ClosedSyncReadyRead (ready : HostReady (HostState sig)) (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ task inst thread frames rest,
    state.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
      syncLiftCandidates task (state.store.instCandidates (ready current) inst))), frames⟩ :: rest ∧
    LinkedCallback.ReadyAgreement ready state inst

/-- The actual reached read produces the same continuation for any host journal. This makes
no assertion about future reads or the existence of a runnable thread. -/
def ClosedHostRead (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ thread resume frames rest,
    state.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest ∧
    ∀ host, resume state.host = resume host

/-- Parameters obtained from the reached callout checks and live handle lookup. -/
structure WaitableCalloutEntry where
  inst : InstId
  set : WsetId
  ptr : Nat

/-- Shared by the early and actually resumed wait. Selection reads the
current store at this point, not the event checked by the readiness read. -/
def waitableWaitContinue (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry) : Session grow sig (Ret (core3 grow)) := do
  modifyStore (CStore.wsetDecWaitingSt entry.set)
  let event ← wsetGetPendingEvent entry.set
  let code ← unpackEvent (Builtins.eventCx mem entry.inst) entry.ptr event
  pure (.flat [i32Flat code])

/-- The continuation after the optional synchronous cancellation wait.
Release the current sync waiter and recheck the current resolution. -/
def cancelFinish (subtask : SubtaskId) : Session grow sig (Ret (core3 grow)) := do
  modifyStore (CStore.setSyncWaiterSt (.subtask subtask) none)
  if ← Builtins.subtaskResolvedNow subtask then
    return .flat (← Builtins.subtaskCancelDeliver subtask)
  else return .flat [i32Flat (AsyncRef.subtaskCancelResult none)]

/-- The first executed action not covered by the closed callback rules.
This is a proof cut, not a new runtime rejection. -/
inductive CallbackWorkerBoundary (bindings : List (Binding sig)) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop)
    (before : Config (core3 grow) (HostState sig)) (label : Label (core3 grow) (HostState sig))
    (next : Config (core3 grow) (HostState sig)) : Prop where
  | give (install : GiveInstall bindings dispatch before label next)
  | componentInstall {active hostId caller resume frames rest}
      (focus : before.ctl = ⟨some active, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest)
  | pollInstall {thread core resume frames rest mem inst args}
      (focus : before.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
      (calling : (core3 grow).status before.store.core core = .callout (.builtin (.waitableSetPoll mem) inst) args)
  | waitInstall {thread core resume frames rest mem inst args}
      (focus : before.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
      (calling : (core3 grow).status before.store.core core = .callout (.builtin (.waitableSetWait mem) inst) args)
  | cancelInstall {thread core resume frames rest async inst args}
      (focus : before.ctl = ⟨thread, .core core resume, frames⟩ :: rest)
      (calling : (core3 grow).status before.store.core core = .callout (.builtin (.subtaskCancel async) inst) args)
  | waitResume {waiter resumer afterResume frames rest core resume savedFrames mem entry}
      (focus : before.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest)
      (found : before.cont? waiter = some ⟨some waiter, .prog (waitableWaitContinue mem entry), .core core resume :: savedFrames⟩)
  | cancelResume {waiter resumer afterResume frames rest core resume savedFrames subtask}
      (focus : before.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest)
      (found : before.cont? waiter = some ⟨some waiter, .prog (cancelFinish subtask), .core core resume :: savedFrames⟩)
  | read {thread resume frames rest}
      (focus : before.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
      (openRead : ¬ ClosedHostRead before)
  | protectedPop {thread value resume frames rest} (retained : protectedReturn resume)
      (focus : before.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest)
  | write {thread value resume frames rest}
      (focus : before.ctl = ⟨thread, .prog (.op (.hostSet value) resume), frames⟩ :: rest)
  | nonGrowingUpdate (failed : ¬ CoreUpdateGrows before)

/-- Every initial occurrence follows the same reached coordinate on both
paths, even if checked journal steps add silent labels. This includes saved
locations and records loss without assuming later return. -/
def CoupledOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∀ cursor : Option Location, ∃ reached,
    Trail profile ready (specDispatch ready base) checkEntry cursor checkTrace checked reached ∧
    Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonEntry cursor canonTrace canonical reached

/-- The same occurrence map both witnesses the machine paths and transports
the older relation around every enclosing mark. In particular a fresh
frame cannot take the place of a lost occurrence. -/
def OccurrenceTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) (introduced : List (Option ReturnFrame.Occurrence.Location) := []) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ move : Option Location → Option Location,
    (∀ cursor, Trail profile ready (specDispatch ready base) checkEntry cursor checkTrace checked (move cursor) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonEntry cursor canonTrace canonical (move cursor)) ∧
    ∀ older marks, OutsideMarks older (segmentStorage checkEntry) (segmentStorage canonEntry) marks →
      OutsideMarks older (segmentStorage checked) (segmentStorage canonical) (introduced ++ marks.map move)

/-- Compare the scheduler and all enclosing continuations while the focused
component programs carry distinct diagnostic data. Normalizing the focus is
only a relation on configurations, not a machine transition. -/
def PairedComponentSite (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig))
    (leftCursor rightCursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  HostFrame.Related.Paired changes
    { left with ctl := leftCursor.control (.pure (.cancel .none)) }
    { right with ctl := rightCursor.control (.pure (.cancel .none)) }

/-- The operations that can be compared using just the reached shared store
and active thread, without consulting either embedder. -/
def componentStoreOp : (Eff (core3 grow) (HostState sig)).Op → Bool
  | .get | .modify _ | .currentThread | .choose _ | .trap _ => true
  | _ => false

def waitableCalloutHost (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) : CanonHost (core3 grow) :=
  .builtin (if poll then .waitableSetPoll mem else .waitableSetWait mem) inst

/-- The shared entry of the public poll and wait programs, before either can
select an event or change the waiter's count. -/
def waitableCalloutEntry (poll : Bool) (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue) :
    Session grow sig WaitableCalloutEntry := do
  let thread ← currentThread
  let store ← getStore
  match calloutEntry store thread (waitableCalloutHost poll mem inst) with
  | some reason => trap reason
  | none => withArgs2 args fun index ptr => do
    let current ← Builtins.enterWaitableBuiltin
    let set ← Builtins.expectWset (← handlesGet current index)
    pure ⟨current, set, ptr⟩

def waitableCalloutBody (poll : Bool) (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry) :
    Session grow sig (Ret (core3 grow)) := do
  let event ← if poll then wsetPoll entry.set else wsetWait entry.set
  let code ← unpackEvent (Builtins.eventCx mem entry.inst) entry.ptr event
  pure (.flat [i32Flat code])

/-- Checked entry of public cancellation before the request write or event
take. A resolved subtask requires no hook; an unresolved one retains the
reached cancellation reference, including a no-op hook. -/
def cancelCalloutEntry (async : Bool) (inst : InstId) (args : List FlatValue) :
    Session grow sig (SubtaskId × Option CancelRef) := do
  let thread ← currentThread
  let store ← getStore
  match calloutEntry store thread (.builtin (.subtaskCancel async) inst) with
  | some reason => trap reason
  | none => withArgs1 args fun index => do
    let current ← Builtins.enterWaitableBuiltin
    let subtask ← Builtins.expectSubtask (← handlesGet current index)
    trapIf (← Subtask.resolveDelivered subtask) .subtaskCancelTwice
    let record ← getObj ArenaField.subtasks subtask
    trapIf record.cancellationRequested .subtaskCancelTwice
    trapIf (← Runtime.Waitable.inWaitableSet (.subtask subtask)) .subtaskInSet
    pure (subtask, if record.state.resolved then none else some record.onCancel)

def cancelCalloutBody (async : Bool) (entry : SubtaskId × Option CancelRef) : Session grow sig (Ret (core3 grow)) := do
  let (subtask, hook) := entry
  match hook with
  | none => return .flat (← Builtins.subtaskCancelDeliver subtask)
  | some hook =>
    if ← Builtins.subtaskCancelRequest async subtask hook then
      return .flat (← Builtins.subtaskCancelDeliver subtask)
    else return .flat [i32Flat (AsyncRef.subtaskCancelResult none)]

def cancelRequestWrite (subtask : SubtaskId) : Session grow sig Unit := do
  let thread ← currentThreadId
  modifyStore (Builtins.WaitableSt.requestCancel subtask thread)

def cancelHookReturn (async : Bool) (subtask : SubtaskId) (result : Ret (core3 grow)) : Session grow sig (Ret (core3 grow)) := do
  let unitResult : Session grow sig Unit := match result with
    | .unit => pure ()
    | _ => internal "late-bound call: expected Ret.unit"
  unitResult
  Builtins.subtaskCancelSyncWait async subtask
  modifyStore (CStore.setSyncWaiterSt (.subtask subtask) none)
  if ← Builtins.subtaskResolvedNow subtask then
    return .flat (← Builtins.subtaskCancelDeliver subtask)
  else return .flat [i32Flat (AsyncRef.subtaskCancelResult none)]

def cancelAfterRequestWrite (async : Bool) (subtask : SubtaskId) (hook : CancelRef) : Session grow sig (Ret (core3 grow)) :=
  .op (.call (.onCancel hook)) (cancelHookReturn async subtask)

def cancelSyncDecision (async : Bool) (subtask : SubtaskId) : Session grow sig (Option ThreadId) := do
  let resolved ← Builtins.subtaskResolvedNow subtask
  if !async && !resolved then
    let thread ← currentThreadId
    let now ← Thread.readyNow (fun _ _ => false) (.subtaskResolved subtask)
    let early ← (if now then choose (.earlyReturn .syncSubtaskCancel) else pure false : Session grow sig Bool)
    if early then pure none else do
      Thread.startWaiting thread (.subtaskResolved subtask)
      pure (some thread)
  else pure none

/-- A hook return is not a public reply. Preserve the ordinary result-type
trap and, for a unit return, the executed async/sync readiness decision. -/
def cancelHookDecision (async : Bool) (subtask : SubtaskId) (result : Ret (core3 grow)) :
    Session grow sig (Option ThreadId) :=
  match result with
  | .unit => cancelSyncDecision async subtask
  | _ => internal "late-bound call: expected Ret.unit"

def cancelAfterHookDecision (subtask : SubtaskId) : Option ThreadId → Session grow sig (Ret (core3 grow))
  | none => cancelFinish subtask
  | some _ => block none >>= fun _ => cancelFinish subtask

/-- Cancellation consumes the currently reached event before reading the result state.
The event records what was delivered; only the result code is returned to Core. -/
def cancelDeliveryObservation (subtask : SubtaskId) : Session grow sig (AsyncRef.EventTuple × Nat) := do
  let event ← Runtime.Waitable.getPendingEvent (.subtask subtask)
  let record ← getObj ArenaField.subtasks subtask
  pure (event, AsyncRef.subtaskCancelResult (some record.state))

/-- Recheck at the reached finish, not at the hook install or wait decision.
Returning `[BLOCKED]` does not consume any pending event. -/
def cancelFinishObservation (subtask : SubtaskId) : Session grow sig (Option AsyncRef.EventTuple × Nat) := do
  modifyStore (CStore.setSyncWaiterSt (.subtask subtask) none)
  if ← Builtins.subtaskResolvedNow subtask then
    let (event, code) ← cancelDeliveryObservation subtask
    pure (some event, code)
  else pure (none, AsyncRef.subtaskCancelResult none)

/-- Record the event consumed by the public poll's actual buffer program.
Only the code becomes a flat result for Core. -/
def pollCalloutObservation (mem : (core3 grow).MemAddr) (inst : InstId) (args : List FlatValue) :
    Session grow sig (AsyncRef.EventTuple × Nat) := do
  let entry ← waitableCalloutEntry true mem inst args
  let event ← wsetPoll entry.set
  let code ← unpackEvent (Builtins.eventCx mem entry.inst) entry.ptr event
  pure (event, code)

def waitableFlatReply (observation : AsyncRef.EventTuple × Nat) : Session grow sig (Ret (core3 grow)) :=
  .pure (.flat [i32Flat observation.2])

/-- Run the actual waiter count update, readiness read and optional early
choice. A non-early answer commits the waiting record but has not blocked. -/
def waitableWaitDecision (entry : WaitableCalloutEntry) : Session grow sig (Option ThreadId) := do
  modifyStore (CStore.wsetIncWaitingSt entry.set)
  let thread ← currentThreadId
  let now ← Thread.readyNow (fun _ _ => false) (.wsetHasEvent entry.set)
  let early ← (if now then choose (.earlyReturn .waitableSetWait) else pure false : Session grow sig Bool)
  if early then pure none else do
    Thread.startWaiting thread (.wsetHasEvent entry.set)
    pure (some thread)

def waitableWaitAfterDecision (mem : (core3 grow).MemAddr) (entry : WaitableCalloutEntry) :
    Option ThreadId → Session grow sig (Ret (core3 grow))
  | none => waitableWaitContinue mem entry
  | some _ => block none >>= fun _ => waitableWaitContinue mem entry

/-- The frontier of an executed store-only component prefix. A pending
operation is not a refusal, and a trap does not run either continuation. -/
inductive ComponentStoreFrontier {Result : Type}
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext canonNext : Result → Session grow sig (Ret (core3 grow)))
    (left right : Config (core3 grow) (HostState sig)) (suffix : Trace grow sig)
    (closed : Prop := False) : Prop where
  | returned (result : Result)
      (checked : left.ctl = check.control (checkNext result))
      (canonical : right.ctl = canon.control (canonNext result))
      (paired : PairedComponentSite older left right check canon)
  | pending (op : (Eff (core3 grow) (HostState sig)).Op)
      (next : (Eff (core3 grow) (HostState sig)).Resp op → Session grow sig Result)
      (checked : left.ctl = check.control (.op op (fun response => next response >>= checkNext)))
      (canonical : right.ctl = canon.control (.op op (fun response => next response >>= canonNext)))
      (paired : PairedComponentSite older left right check canon)
      (boundary : suffix = [] ∨ (¬ closed ∧ componentStoreOp op = false))
  | trapped (checked : left.ctl = []) (canonical : right.ctl = [])
      (paired : HostFrame.Related.Paired older left right)

/-- The end of an actual finite flat-result callout cut. At reply focus the installed
caller is still live; only the rejoined case consumes its original slot. -/
inductive FlatCalloutExit {Observation : Type} (code : Observation → Nat)
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) (suffix : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | exhausted (noMore : suffix = []) (endpoint : finish = left)
  | trapped (checked : left.ctl = []) (canonical : right.ctl = []) (paired : HostFrame.Related.Paired older left right)
  | rejoined (observation : Observation) {thread core resume frames rest peerFrames peerRest remaining}
      (checked : left.ctl = ⟨thread, .prog (.pure (.flat [i32Flat (code observation)])), .core core resume :: frames⟩ :: rest)
      (canonical : right.ctl = ⟨thread, .prog (.pure (.flat [i32Flat (code observation)])), .core core resume :: peerFrames⟩ :: peerRest)
      (split : suffix = .tau :: remaining)
      (residual : Steps profile ready (specDispatch ready base)
        { left with ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values [i32Flat (code observation)])) resume,
          frames⟩ :: rest } remaining finish)
      (paired : HostFrame.Related.Paired older
        { left with ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values [i32Flat (code observation)])) resume,
          frames⟩ :: rest }
        { right with ctl := ⟨thread, .core ((core3 grow).resume right.store.core core (.values [i32Flat (code observation)])) resume,
          peerFrames⟩ :: peerRest })
      (pop : OccurrenceTransport profile ready base bindings left right [.tau] [.tau]
        { left with ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values [i32Flat (code observation)])) resume,
          frames⟩ :: rest }
        { right with ctl := ⟨thread, .core ((core3 grow).resume right.store.core core (.values [i32Flat (code observation)])) resume,
          peerFrames⟩ :: peerRest })

abbrev WaitableCalloutExit := FlatCalloutExit (grow := grow) (sig := sig) (Prod.snd : AsyncRef.EventTuple × Nat → Nat)

abbrev CancelFinishExit := FlatCalloutExit (grow := grow) (sig := sig) (Prod.snd : Option AsyncRef.EventTuple × Nat → Nat)

/-- The reached endpoint of a successful validation path. Publication can
reach the reply focus without returning to the caller or delivering an event. -/
inductive ComponentAcceptedFrontier
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (tree : Stored.OwnedMemory.Tree sig) (handle : Nat)
    (left right : Config (core3 grow) (HostState sig)) (suffix : Trace grow sig) : Prop where
  | pending (paired : PairedComponentSite older left right check canon) (exhausted : suffix = [])
  | trapped (checked : left.ctl = []) (canonical : right.ctl = [])
      (paired : HostFrame.Related.Paired older left right)
  | published (checked : left.ctl = check.control (.pure (.cancel .none)))
      (canonical : right.ctl = canon.control (.pure (.cancel .none)))
      (paired : HostFrame.Related.Paired older left right)
      (checkedLookup : Stored.Endpoints.Core.childFromHistory left.host.writer.accepted (BitVec.ofNat 32 handle) = some tree)
      (canonicalLookup : Stored.Endpoints.Core.childFromHistory right.host.writer.accepted (BitVec.ofNat 32 handle) = some tree)

/-- A finite input ending before a component protocol reaches its common
program. Both endpoints are at their original component cursors, with separate
focused programs and journals; the selected and enclosing occurrences follow
the actual consumed steps. -/
def ComponentEarlyPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) (limit : Nat) : Prop :=
  labels.length < limit ∧ ∃ peer,
    OccurrenceTransport profile ready base bindings start incoming labels labels finish peer ∧
    PairedComponentSite older finish peer check canon ∧
    (∃ program, finish.ctl = check.control program) ∧ (∃ program, peer.ctl = canon.control program)

/-- The reached host-frame refusal at a direct give. The canonical body has
no entry/completion journal steps; a checked prefix can end before the reply. -/
def DirectHostRefusalCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (name : String) (kind : V1.FuncType)
    (args : List FlatValue) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (entry peerEntry start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  (labels.length < 6 ∧ PayloadPrefix.visible labels = [] ∧
    OccurrenceTransport profile ready base bindings entry peerEntry ([.tau, .tau, .tau] ++ labels) [.tau, .tau, .tau]
      finish incoming [some (.active 0 0)]) ∨
  ∃ trailing left right,
    let reply := giveAdmissionReply start.host.nextTicket destination schema .wrongContext
    labels = List.replicate 6 .tau ++ trailing ∧
    OccurrenceTransport profile ready base bindings entry peerEntry (List.replicate 9 .tau) (List.replicate 5 .tau)
      left right [some (.active 0 0)] ∧
    left.host = (start.host.enter name kind args).record reply.1 ∧ right.host = incoming.host ∧
    left.ctl = check.control (.pure (.flat reply.2)) ∧ right.ctl = canon.control (.pure (.flat reply.2)) ∧
    PairedComponentSite older left right check canon ∧ Steps profile ready (specDispatch ready base) left trailing finish

/-- The direct dispatcher reads the active thread and live store before
entering either embedder body. At a host frame, continue to its refusal. -/
def DirectGivePreludeCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (name : String) (kind : V1.FuncType)
    (args : List FlatValue) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (entry peerEntry start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ComponentEarlyPrefix profile ready base bindings older check canon start incoming labels finish 2 ∨
    ∃ trailing left right,
      labels = [.tau, .tau] ++ trailing ∧ left.host = start.host ∧ right.host = incoming.host ∧
      left.store = start.store ∧ right.store = incoming.store ∧
      left.ctl = check.control (calloutBody Limits.spec Quirks.none ready base left.store check.thread (.embedder name kind) args) ∧
      right.ctl = canon.control (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base)
        right.store canon.thread (.embedder name kind) args) ∧
      PairedComponentSite older left right check canon ∧
      OccurrenceTransport profile ready base bindings entry peerEntry [.tau, .tau, .tau] [.tau, .tau, .tau]
        left right [some (.active 0 0)] ∧
      Steps profile ready (specDispatch ready base) left trailing finish ∧
      (check.thread = none → canon.thread = none →
        DirectHostRefusalCut profile ready base bindings older name kind args destination schema
          check canon entry peerEntry left right trailing finish)

/-- Replay the exact extracted prefix, including silent steps. The selected
mark can move between active and saved storage or disappear; all other
locations also retain their actual scheduler paths. -/
def ActualCallbackReplay (bindings : List (Binding sig)) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (base : HostImpl (core3 grow) (HostState sig))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop)
    (start : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∀ {changes retained peer mark}, (∀ first second, changes first second → protectedReturn first) →
    HostFrame.Related.Paired changes start peer → Outside retained (segmentStorage start) (segmentStorage peer) mark →
    ∃ reached finalMark,
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer labels reached ∧
      HostFrame.Related.Paired changes finish reached ∧
      Outside retained (segmentStorage finish) (segmentStorage reached) finalMark ∧
      Trail profile ready (specDispatch ready base) start mark labels finish finalMark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer mark labels reached finalMark ∧
      CoupledOccurrencePaths profile ready base bindings start peer labels labels finish reached ∧
      OccurrenceTransport profile ready base bindings start peer labels labels finish reached

/-- Extract a closed prefix from the actual finite derivation, leaving any
boundary action and the rest of the checked run at their original states. -/
inductive ClassifiedCallbackRun (bindings : List (Binding sig)) (profile : ProfileKind)
    (ready : HostReady (HostState sig)) (base : HostImpl (core3 grow) (HostState sig))
    (protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop)
    (start : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | complete (closed : ClosedCallbackPrefix bindings profile ready base protectedReturn start (PayloadPrefix.visible labels) finish)
      (replay : ActualCallbackReplay bindings profile ready base protectedReturn start labels finish)
      (growing : CoreGrowthSteps profile ready (specDispatch ready base) start labels finish)
  | boundary {leading label trailing reached next}
      (split : labels = leading ++ label :: trailing)
      (closed : ClosedCallbackPrefix bindings profile ready base protectedReturn start (PayloadPrefix.visible leading) reached)
      (growing : CoreGrowthSteps profile ready (specDispatch ready base) start leading reached)
      (replay : ActualCallbackReplay bindings profile ready base protectedReturn start leading reached)
      (cut : CallbackWorkerBoundary bindings ready (specDispatch ready base) protectedReturn reached label next)
      (actual : Step profile ready (specDispatch ready base) reached label next)
      (tail : Steps profile ready (specDispatch ready base) next trailing finish)

/-- The installed allocator occurrence migrates through actual scheduler
edits. Older substitutions remain valid off that mark, even if it is lost
to a trap or the callback is still suspended. -/
structure AllocatorMark (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) (mark : Option ReturnFrame.Occurrence.Location) : Prop where
  outside : ReturnFrame.Occurrence.Outside older (ReturnFrame.Occurrence.segmentStorage checked)
    (ReturnFrame.Occurrence.segmentStorage canonical) mark
  checkedTrail : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base)
    checkEntry (some (.active 0 0)) checkTrace checked mark
  canonicalTrail : ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
    canonEntry (some (.active 0 0)) canonTrace canonical mark
  movement : CoupledOccurrencePaths profile ready base bindings checkEntry canonEntry checkTrace canonTrace checked canonical

/-- Follow an actual allocation install into an extracted finite callback.
The newly installed occurrence is tracked separately from the enclosing
ones; each may independently move or be lost. -/
def ActualAllocatorOccurrencePrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right checkEntry canonEntry : Config (core3 grow) (HostState sig))
    (checkInstall canonInstall callback : Trace grow sig) (checked : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ canonical mark, HostFrame.Related.Paired changes checked canonical ∧
    AllocatorMark profile ready base bindings older checkEntry canonEntry callback callback checked canonical mark ∧
    OccurrenceTransport profile ready base bindings left right (checkInstall ++ callback) (canonInstall ++ callback)
      checked canonical [mark]

def stringAllocatorEntry (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat) (alignment : ABI.Alignment) (size : Nat)
    (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) : Config (core3 grow) (HostState sig) :=
  let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
  { state with ctl := { cursor with frames := .prog resume :: cursor.frames }.control (dispatch request) }

/-- The executed part of a callback. Its checked and canonical traces are
indexed separately; the reached pair keeps the actual journals. -/
structure ExecutedCallbackSegment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (checkLabels canonLabels : Trace grow sig)
    (finish peer : Config (core3 grow) (HostState sig)) : Prop where
  checkedRun : CoreGrowthSteps profile ready (specDispatch ready base) checked checkLabels finish
  observed : PayloadPrefix.visible canonLabels = PayloadPrefix.visible checkLabels
  paired : HostFrame.Related.Paired changes finish peer
  occurrences : OccurrenceTransport profile ready base bindings checked canonical checkLabels canonLabels finish peer

abbrev CallbackPathIndex (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Option (Trace grow sig × Trace grow sig × Config (core3 grow) (HostState sig))

def CallbackPathIndex.Matches (index : CallbackPathIndex grow sig)
    (checked canonical : Trace grow sig) (peer : Config (core3 grow) (HostState sig)) : Prop :=
  match index with
  | none => True
  | some executed => executed = (checked, canonical, peer)

/-- The callback evidence shared by string and collection traversal. In the
executed case the two prefixes may have different silent steps. Growth is
certified at reached updates on the checked prefix; the journals need not
be preserved. Neither case asserts that the installed occurrence returns. -/
inductive AllocatorCallbackPrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) :
    CallbackPathIndex grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | closed {seen finish} (path : ClosedCallbackPrefix bindings profile ready base
      (fun resume => (∃ peer, older resume peer) ∨ resume = first) checked seen finish) :
      AllocatorCallbackPrefix profile ready base bindings older first second checked canonical none seen finish
  | executed {checkLabels canonLabels finish peer}
      (run : ExecutedCallbackSegment profile ready base bindings (ReturnFrame.Extend older first second)
        checked canonical checkLabels canonLabels finish peer) :
      AllocatorCallbackPrefix profile ready base bindings older first second checked canonical
        (some (checkLabels, canonLabels, peer)) (PayloadPrefix.visible checkLabels) finish

/-- Cut a growing checked derivation at the first action not covered by
closed replay. No part of a boundary action is replayed by this cut. -/
inductive ExecutedCallbackCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | complete {peer} (segment : ExecutedCallbackSegment profile ready base bindings changes checked canonical actual actual finish peer)
  | boundary {leading label trailing reached peer next}
      (split : actual = leading ++ label :: trailing)
      (segment : ExecutedCallbackSegment profile ready base bindings changes checked canonical leading leading reached peer)
      (kind : CallbackWorkerBoundary bindings ready (specDispatch ready base) (fun resume => ∃ rhs, changes resume rhs) reached label next)
      (step : Step profile ready (specDispatch ready base) reached label next)
      (tail : Steps profile ready (specDispatch ready base) next trailing finish)
      (smaller : trailing.length < actual.length)

/-- A typed give reply executed only on the checked side. The canonical
trace ends at the reached pending configuration, not at a matching pop. -/
def CheckedOnlyGiveReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (route : GiveEffectRoute) (destination : RecordDestination) (ticket : Nat)
    (issue : Stored.Endpoints.RecordLower.Issue)
    (start incoming left right : Config (core3 grow) (HostState sig))
    (checkLeading canonLeading trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ suffix checked,
    trailing = [.tau, .tau, .tau] ++ suffix ∧
    Steps profile ready (specDispatch ready base) start checkLeading left ∧
    Steps profile ready (specDispatch ready base) left [.tau, .tau, .tau] checked ∧
    Steps profile ready (specDispatch ready base) checked suffix finish ∧
    checked.store = left.store ∧
    checked.host = left.host.record (route.reply destination ticket (.error issue)).1 ∧
    ∀ cursor : Option Location, ∃ checkedMark canonMark,
      Trail profile ready (specDispatch ready base) start cursor (checkLeading ++ [.tau, .tau, .tau]) checked checkedMark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming cursor canonLeading right canonMark

/-- A checked trace may reach an open store update that cannot be used to
transport a linked-memory width. This is a comparison boundary, not a
runtime refusal, and does not require later updates to preserve growth. -/
def ReachedNonGrowingUpdate (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start : Config (core3 grow) (HostState sig)) (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ leading label trailing reached next,
    labels = leading ++ label :: trailing ∧ CoreGrowthSteps profile ready dispatch start leading reached ∧
    ¬ CoreUpdateGrows reached ∧ Step profile ready dispatch reached label next ∧ Steps profile ready dispatch next trailing finish

def workerBranchLabel : Label (core3 grow) (HostState sig) → Prop
  | .choice _ _ | .host _ => True
  | _ => False

/-- A recursive body stopped before a common caller reply. A local branch
retains the reached checked action, not an invented canonical action. -/
inductive GiveBodyStop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) (trailing : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) (caller : Option ReturnFrame.Occurrence.Location) : Prop where
  | trap (leftLocked : left.ctl = []) (rightLocked : right.ctl = [])
  | localPrefix {target remaining} (nonempty : remaining ≠ [])
      (tail : Steps profile ready (specDispatch ready base) finish remaining target)
  | localChoice {leading taken suffix middle next} (split : trailing = leading ++ taken :: suffix)
      (choice : workerBranchLabel taken) (shared : Steps profile ready (specDispatch ready base) left leading middle)
      (step : Step profile ready (specDispatch ready base) middle taken next)
      (tail : Steps profile ready (specDispatch ready base) next suffix finish)
  | allocatorInstall {count : Nat} (short : trailing.length < count)
  | replyPrefix (refusal : Option Stored.Endpoints.RecordLower.Issue) (short : trailing.length < 3)
  | callerNotTop (refusal : Option Stored.Endpoints.RecordLower.Issue) (missing : caller ≠ some (.active 0 0))

/-- The part of a give actually compared, rebased through its own entry.
Both trails end before executing the checked residual. -/
structure GiveBodyCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start peer left right : Config (core3 grow) (HostState sig))
    (checked canonical trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (marks : List (Option ReturnFrame.Occurrence.Location)) : Prop where
  observed : PayloadPrefix.visible checked = PayloadPrefix.visible canonical
  store : left.store = right.store
  paths : OccurrenceTransport profile ready base bindings start peer checked canonical left right marks
  residual : Steps profile ready (specDispatch ready base) left trailing finish

open ReturnFrame.Occurrence in
/-- The checked-only completion of a direct give. A finite prefix before
the program pop retains its mark; only the actual pop may lose that mark and
start the original caller with the recorded reply. -/
inductive CheckedProgramReplyCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) (start : Config (core3 grow) (HostState sig))
    (caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) (reply : Event × List FlatValue) :
    Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | prefix {actual finish} (short : actual.length < 3)
      (paths : ∀ mark, Trail profile ready dispatch start mark actual finish mark) :
      CheckedProgramReplyCut profile ready dispatch start caller resume reply actual finish
  | popped {trailing finish}
      (written : ∀ place, Prefix profile ready dispatch start place [.tau, .tau]
        { start with
          host := start.host.record reply.1
          ctl := { caller with frames := .prog resume :: caller.frames }.control (.pure (.flat reply.2)) } place)
      (remaining : Steps profile ready dispatch
        { start with
          host := start.host.record reply.1
          ctl := { caller with frames := .prog resume :: caller.frames }.control (.pure (.flat reply.2)) } (.tau :: trailing) finish)
      (paths : ∀ mark, Trail profile ready dispatch start mark [.tau, .tau, .tau]
        { start with host := start.host.record reply.1, ctl := caller.control (resume (.flat reply.2)) }
        (mark.bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow))
      (residual : Steps profile ready dispatch
        { start with host := start.host.record reply.1, ctl := caller.control (resume (.flat reply.2)) } trailing finish) :
      CheckedProgramReplyCut profile ready dispatch start caller resume reply ([.tau, .tau, .tau] ++ trailing) finish

open ReturnFrame.Occurrence in
/-- Placement is an actual checked path. The canonical program stays
pending; a placement fault alone does not evidence a canonical fault. -/
inductive DirectGivePlacementCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start peer : Config (core3 grow) (HostState sig))
    (caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (request : GiveSelector bindings) (ticket : Nat) (selected : SelectionValue sig request.schema)
    (field : Stored.Endpoints.RecordLower.Field) : Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | prefix {actual finish}
      (paths : ∀ mark, ∃ reached, Trail profile ready (specDispatch ready base) start mark actual finish reached)
      (pending : ∃ suffix, suffix ≠ [] ∧ ∃ target, Steps profile ready (specDispatch ready base) finish suffix target) :
      DirectGivePlacementCut profile ready base bindings start peer caller resume request ticket selected field actual finish
  | trapped {reason count trailing finish}
      (placement : request.selectedPlacement selected start.store = .error reason)
      (paths : ∀ mark, Trail profile ready (specDispatch ready base) start mark (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg start) (mark.bind (Edit.clear : Edit (core3 grow) (HostState sig)).follow))
      (residual : Steps profile ready (specDispatch ready base) (StepDefs.trapCfg start) trailing finish) :
      DirectGivePlacementCut profile ready base bindings start peer caller resume request ticket selected field
        ((List.replicate count .tau ++ [.trap reason]) ++ trailing) finish
  | reached {used trailing finish}
      (after : Config (core3 grow) (HostState sig))
      (focus : after = { start with
        ctl := { caller with frames := .prog resume :: caller.frames }.control (request.fieldContinuation ticket selected field) })
      (placement : request.selectedPlacement selected start.store = .ok ())
      (paths : ∀ place, Prefix profile ready (specDispatch ready base) start place used after place)
      (quiet : PayloadPrefix.visible used = [])
      (residual : Steps profile ready (specDispatch ready base) after trailing finish) :
      DirectGivePlacementCut profile ready base bindings start peer caller resume request ticket selected field (used ++ trailing) finish

open ReturnFrame.Occurrence in
/-- A finite cut at the real width read. Fit is decided in the reached
continuation; the peer still has its original canonical program pending. -/
inductive DirectGiveWidthCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start peer : Config (core3 grow) (HostState sig))
    (caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (request : GiveSelector bindings) (ticket : Nat) (selected : SelectionValue sig request.schema)
    (field : Stored.Endpoints.RecordLower.Field) : Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | prefix (paths : OccurrenceTransport profile ready base bindings start peer [] [] start peer) :
      DirectGiveWidthCut profile ready base bindings start peer caller resume request ticket selected field [] start
  | reached {trailing finish}
      (after : Config (core3 grow) (HostState sig))
      (focus : after = { start with
        ctl := { caller with frames := .prog resume :: caller.frames }.control
          (request.measuredContinuation ticket selected field (ptrTypeIn start.store (request.destination.context request.inst))) })
      (paths : ∀ place, Prefix profile ready (specDispatch ready base) start place [.tau] after place)
      (residual : Steps profile ready (specDispatch ready base) after trailing finish)
      (decision : let width := ptrTypeIn start.store (request.destination.context request.inst)
        (request.selectedFits selected width = false ∧
          CheckedProgramReplyCut profile ready (specDispatch ready base) after caller resume
            (giveAdmissionReply ticket request.destination request.schema (.lowerPayload (.preflight (.abi .allocationPrecondition))))
            trailing finish) ∨
        (request.selectedFits selected width = true ∧
          after.ctl = { caller with frames := .prog resume :: caller.frames }.control
            (request.placementContinuation ticket selected field width) ∧
          DirectGivePlacementCut profile ready base bindings after peer caller resume request ticket selected field trailing finish)) :
      DirectGiveWidthCut profile ready base bindings start peer caller resume request ticket selected field (.tau :: trailing) finish

open ReturnFrame.Occurrence in
/-- A finite checked cut at the compiled root's preparation reads. No
canonical step is spent by these checked-only reads. -/
inductive DirectGivePreparationCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start peer : Config (core3 grow) (HostState sig))
    (caller : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (request : GiveSelector bindings) (ticket : Nat) (selected : SelectionValue sig request.schema)
    (field : Stored.Endpoints.RecordLower.Field) : Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | prefix {actual finish} (short : actual.length < 2)
      (paths : OccurrenceTransport profile ready base bindings start peer actual [] finish peer) :
      DirectGivePreparationCut profile ready base bindings start peer caller resume request ticket selected field actual finish
  | reached {trailing finish}
      (after : Config (core3 grow) (HostState sig))
      (focus : after = { start with
        ctl := { caller with frames := .prog resume :: caller.frames }.control
          (request.preparedContinuation ticket selected field (Record.prepare start.store start.host.writer field.objects)) })
      (paths : ∀ place, Prefix profile ready (specDispatch ready base) start place [.tau, .tau] after place)
      (residual : Steps profile ready (specDispatch ready base) after trailing finish)
      (refused : ∀ issue, Record.prepare start.store start.host.writer field.objects = .error issue →
        CheckedProgramReplyCut profile ready (specDispatch ready base) after caller resume
          (giveAdmissionReply ticket request.destination request.schema (.lowerPayload issue)) trailing finish)
      (prepared : Record.prepare start.store start.host.writer field.objects = .ok () →
        DirectGiveWidthCut profile ready base bindings after peer caller resume request ticket selected field trailing finish) :
      DirectGivePreparationCut profile ready base bindings start peer caller resume request ticket selected field
        ([.tau, .tau] ++ trailing) finish

/-- The terminal cut of a compared callback. In-body cuts keep the exact
give prefix before a residual; an inner allocator cut can itself diverge. -/
inductive CallbackSliceEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) :
    ReturnFrame.Substitutions (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | exhausted {changes reached peer} : CallbackSliceEnd profile ready base bindings changes reached peer [] reached
  | boundary {changes reached peer label next trailing finish}
      (kind : CallbackWorkerBoundary bindings ready (specDispatch ready base) (fun resume => ∃ peer, changes resume peer)
        reached label next)
      (step : Step profile ready (specDispatch ready base) reached label next)
      (tail : Steps profile ready (specDispatch ready base) next trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (label :: trailing) finish
  | observation {changes reached peer next otherNext trailing finish thread resume frames rest}
      (focus : reached.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
      (different : resume reached.host ≠ resume peer.host)
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] next otherNext)
      (tail : Steps profile ready (specDispatch ready base) next trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (.tau :: trailing) finish
  | refused {changes reached peer label next route destination ticket issue left right checkLeading canonLeading trailing finish}
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (observed : PayloadPrefix.visible canonLeading = PayloadPrefix.visible checkLeading)
      (reply : CheckedOnlyGiveReply profile ready base bindings route destination ticket issue reached peer left right
        checkLeading canonLeading trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checkLeading ++ trailing) finish
  | entryPrefix {changes reached peer label next actual finish entry remaining}
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (run : Steps profile ready (specDispatch ready base) reached actual finish) (nonempty : remaining ≠ [])
      (rest : Steps profile ready (specDispatch ready base) finish remaining entry) :
      CallbackSliceEnd profile ready base bindings changes reached peer actual finish
  | directGiveEntry {changes reached peer left right name kind args inst destination schema resume check canon trailing finish}
      (linked : resolveBinding bindings name kind =
        .ok ⟨name, inst, Option.elim schema (.givePayload destination) (.giveFlat destination)⟩)
      (checkedFocus : left.ctl = check.control (specDispatch ready base (.hostCallout (.embedder name kind) args)))
      (canonicalFocus : right.ctl = canon.control
        (specDispatch ready (LiveDispatch.host bindings base) (.hostCallout (.embedder name kind) args)))
      (site : PairedComponentSite changes left right check canon)
      (paths : OccurrenceTransport profile ready base bindings reached peer [.tau] [.tau] left right [some (.active 0 0)])
      (checkedMark : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage left) (.active 0 0) = some (.prog resume))
      (canonicalMark : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage right) (.active 0 0) = some (.prog resume))
      (prelude : DirectGivePreludeCut profile ready base bindings changes name kind args destination schema
        check canon reached peer left right trailing finish)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (.tau :: trailing) finish
  | lookup {changes reached peer label next trailing finish handle} (request : CoreGiveRequest bindings reached)
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (demand : request.lookupDemand = some handle)
      (different : Stored.Endpoints.Core.childFromHistory reached.host.writer.accepted handle ≠
        Stored.Endpoints.Core.childFromHistory peer.host.writer.accepted handle)
      (residual : Steps profile ready (specDispatch ready base) next trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (label :: trailing) finish
  | admissionTrap {changes reached peer label next leftCount rightCount reason trailing finish}
      (request : CoreGiveRequest bindings reached)
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (caller : Plain.callerInstance reached.store request.thread = .error (.trapped reason))
      (checked : Steps profile ready (specDispatch ready base) reached (List.replicate leftCount .tau ++ [.trap reason])
        (StepDefs.trapCfg { reached with host := reached.host.enter request.name request.kind request.args }))
      (canonical : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer
        (List.replicate rightCount .tau ++ [.trap reason]) (StepDefs.trapCfg peer))
      (residual : Steps profile ready (specDispatch ready base)
        (StepDefs.trapCfg { reached with host := reached.host.enter request.name request.kind request.args }) trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer ((List.replicate leftCount .tau ++ [.trap reason]) ++ trailing) finish
  | directGiveTrap {changes reached peer left right checked canonical trailing finish reason}
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish [none])
      (trapped : PayloadPrefix.visible checked = [.trap reason])
      (checkedLocked : left.ctl = []) (canonicalLocked : right.ctl = []) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | directGiveLookupMismatch {changes reached peer left right checked canonical trailing finish resume handle}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (request : GiveSelector bindings)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish [some (.active 0 0)])
      (site : PairedComponentSite changes left right
        { check with frames := .prog resume :: check.frames } { canon with frames := .prog resume :: canon.frames })
      (checkedFocus : left.ctl = { check with frames := .prog resume :: check.frames }.control
        (calloutBody Limits.spec Quirks.none ready base left.store check.thread (.embedder request.name request.kind) request.args))
      (canonicalFocus : right.ctl = { canon with frames := .prog resume :: canon.frames }.control
        (calloutBody Limits.spec Quirks.none ready (LiveDispatch.host bindings base) right.store canon.thread
          (.embedder request.name request.kind) request.args))
      (demand : request.lookupDemand left.store check.thread = some handle)
      (different : Stored.Endpoints.Core.childFromHistory left.host.writer.accepted handle ≠
        Stored.Endpoints.Core.childFromHistory right.host.writer.accepted handle) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | directGiveSelected {changes reached peer left right checked canonical trailing finish resume ticket}
      {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
      (request : GiveSelector bindings) (selected : SelectionValue sig request.schema)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish [some (.active 0 0)])
      (admission : request.Admitted left check.thread selected)
      (site : PairedComponentSite changes left right
        { check with frames := .prog resume :: check.frames } { canon with frames := .prog resume :: canon.frames })
      (checkedFocus : left.ctl = { check with frames := .prog resume :: check.frames }.control
        (request.checkedContinuation left.store check.thread (ticket, .ok selected)))
      (canonicalFocus : right.ctl = { canon with frames := .prog resume :: canon.frames }.control
        (referenceTail request.inst request.destination request.schema (.ok selected) >>= fun reply => pure (.flat reply)))
      (compiler : (∃ field plan, request.preflight (grow := grow) selected = .ok (field, plan) ∧
          left.ctl = { check with frames := .prog resume :: check.frames }.control
            (request.compiledContinuation ticket selected field plan) ∧
          DirectGivePreparationCut profile ready base bindings left right check resume request ticket selected field trailing finish) ∨
        ∃ issue, request.preflight (grow := grow) selected = .error issue ∧
          CheckedProgramReplyCut profile ready (specDispatch ready base) left check resume
            (giveAdmissionReply ticket request.destination request.schema (.lowerPayload issue)) trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | compilerRefused {changes reached peer label next count canonLabels entered issue trailing finish route}
      {request : CoreGiveRequest bindings reached} (selection : request.Selected route)
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (refused : selection.preflight = .error issue)
      (checked : ∀ place : ReturnFrame.Occurrence.Location,
        ReturnFrame.Occurrence.Trail profile ready (specDispatch ready base) reached (some place)
          (List.replicate count .tau) (selection.compilerRefused issue) (some place))
      (canonical : ∀ place : ReturnFrame.Occurrence.Location,
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer place canonLabels entered
          (((ReturnFrame.Occurrence.Edit.push (.core request.core request.next)).follow place).getD place))
      (quiet : PayloadPrefix.visible canonLabels = [])
      (pending : HostFrame.Related.Paired changes selection.canonicalPending entered)
      (host : entered.host = peer.host)
      (residual : Steps profile ready (specDispatch ready base) (selection.compilerRefused issue) trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (List.replicate count .tau ++ trailing) finish
  | placementTrap {changes peer label next count canonLabels entered reason trailing finish route}
      (site : PayloadRoot.Site grow sig route)
      (install : GiveInstall bindings (specDispatch ready base) site.start label next)
      (failed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .error reason)
      (checked : site.EntryTrap profile ready base (List.replicate count .tau ++ [.trap reason]))
      (canonical : ∀ place : ReturnFrame.Occurrence.Location,
        ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer place canonLabels entered
          (site.entryPlace place))
      (quiet : PayloadPrefix.visible canonLabels = [])
      (pending : HostFrame.Related.Paired changes (site.reference site.referenceReply) entered)
      (host : entered.host = peer.host)
      (residual : Steps profile ready (specDispatch ready base) (StepDefs.trapCfg site.checked) trailing finish) :
      CallbackSliceEnd profile ready base bindings changes site.start peer ((List.replicate count .tau ++ [.trap reason]) ++ trailing) finish
  | body {changes reached peer label next left right checked canonical trailing finish marks caller}
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish (marks ++ [caller]))
      (stop : GiveBodyStop profile ready base left right trailing finish caller) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | allocator {changes reached peer label next left right checked canonical trailing finish caller
      checkEntry canonEntry checkLabels canonLabels mark first second}
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (cut : GiveBodyCut profile ready base bindings reached peer left right checked canonical trailing finish [mark, caller])
      (tracked : AllocatorMark profile ready base bindings changes checkEntry canonEntry checkLabels canonLabels left right mark)
      (paired : HostFrame.Related.Paired (ReturnFrame.Extend changes first second) left right)
      (ending : CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend changes first second) left right trailing finish)
      (notPopped : trailing = [] ∨ mark ≠ some (.active 0 0) ∨ ¬ ∃ (pointer : Nat)
        (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
        left.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer))) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | uncertified {changes reached peer label next left right checked canonical trailing finish}
      (install : GiveInstall bindings (specDispatch ready base) reached label next)
      (update : ReachedNonGrowingUpdate profile ready (specDispatch ready base) reached checked left)
      (paired : HostFrame.Related.Paired changes left right)
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right)
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | pollTerminal {changes reached peer left right checked trailing finish mark check canon}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked checked left right [mark])
      (frontier : ComponentStoreFrontier changes check canon waitableFlatReply waitableFlatReply left right trailing True)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | waitTerminal {changes reached peer left right checked trailing finish check canon marks} {Result : Type}
      {next : Result → Session grow sig (Ret (core3 grow))}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked checked left right marks)
      (frontier : ComponentStoreFrontier changes check canon next next left right trailing True)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | cancelTerminal {changes reached peer left right checked canonical trailing finish marks}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right marks)
      (observed : PayloadPrefix.visible canonical = PayloadPrefix.visible checked)
      (exit : CancelFinishExit profile ready base bindings changes left right trailing finish)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | cancelHookBody {changes reached peer left right entry peerEntry checked canonical hookChecked hookCanonical trailing
        finish mark marks resume}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right marks)
      (observed : PayloadPrefix.visible checked = PayloadPrefix.visible canonical)
      (hook : AllocatorMark profile ready base bindings changes entry peerEntry hookChecked hookCanonical left right mark)
      (ending : CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend changes resume resume) left right trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | cancelDecisionTerminal {changes reached peer left right checked canonical trailing finish check canon subtask marks}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right marks)
      (observed : PayloadPrefix.visible canonical = PayloadPrefix.visible checked)
      (frontier : ComponentStoreFrontier changes check canon (cancelAfterHookDecision subtask) (cancelAfterHookDecision subtask)
        left right trailing True)
      (terminal : trailing = [] ∨ (left.ctl = [] ∧ right.ctl = []))
      (residual : Steps profile ready (specDispatch ready base) left trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish
  | cancelParked {changes reached peer left right checked canonical trailing finish mark}
      (paths : OccurrenceTransport profile ready base bindings reached peer checked canonical left right [mark])
      (observed : PayloadPrefix.visible canonical = PayloadPrefix.visible checked)
      (ending : CallbackSliceEnd profile ready base bindings changes left right trailing finish) :
      CallbackSliceEnd profile ready base bindings changes reached peer (checked ++ trailing) finish

def CallbackSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels trailing reached peer,
    actual = checkLabels ++ trailing ∧
    ExecutedCallbackSegment profile ready base bindings changes checked canonical checkLabels canonLabels reached peer ∧
    CallbackSliceEnd profile ready base bindings changes reached peer trailing finish

/-- Start with the original active Core slot at a callout block and follow it
through the compared part of the mixed suffix, including actual resumes.
The ending retains the unconsumed checked residual. An absent occurrence
does not identify a later, equal saved frame as the original waiter. -/
def ParkedCoreCalloutSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (changes : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  (actual = [] ∧ finish = checked) ∨
    ∃ checkLabels canonLabels trailing reached peer mark,
      actual = (.tau :: checkLabels) ++ trailing ∧
      OccurrenceTransport profile ready base bindings checked canonical (.tau :: checkLabels) (.tau :: canonLabels) reached peer ∧
      Trail profile ready (specDispatch ready base) checked (some (.active 0 0)) (.tau :: checkLabels) reached mark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical (some (.active 0 0))
        (.tau :: canonLabels) peer mark ∧
      CallbackSliceEnd profile ready base bindings changes reached peer trailing finish

abbrev ParkedWaitCallbackSlice := ParkedCoreCalloutSlice (grow := grow) (sig := sig)

/-- The induction hypothesis available inside a reached give, including
callbacks with freshly extended substitutions. -/
def ShorterCallbackSlices (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) (budget : Nat) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical finish actual},
    actual.length < budget → Steps profile ready (specDispatch ready base) checked actual finish →
    HostFrame.Related.Paired changes checked canonical → CallbackSlice profile ready base bindings changes checked canonical actual finish

/-- A local give rule for the callback fold, called only at an extracted
install. To advance it must consume that install in a compared segment and
leave a checked residual from the supplied derivation. An unclassified
boundary is not a runtime refusal. -/
def CallbackGiveCrossing (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) : Prop :=
  ∀ {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {checked canonical next finish label trailing},
    GiveInstall bindings (specDispatch ready base) checked label next →
    Steps profile ready (specDispatch ready base) next trailing finish →
    HostFrame.Related.Paired changes checked canonical →
    ShorterCallbackSlices profile ready base bindings (label :: trailing).length →
    (∃ consumed canonLabels residual replied peer,
      trailing = consumed ++ residual ∧
      ExecutedCallbackSegment profile ready base bindings changes checked canonical (label :: consumed) canonLabels replied peer ∧
      Steps profile ready (specDispatch ready base) replied residual finish) ∨
    CallbackSlice profile ready base bindings changes checked canonical (label :: trailing) finish

/-- The silent install is available before comparing a callback, so the
recursive consumer can enter the actual checked tail at these coordinates. -/
structure PairedAllocatorInstall (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (checked canonical checkEntry canonEntry : Config (core3 grow) (HostState sig))
    (checkCount canonCount : Nat) : Prop where
  checkedRun : Steps profile ready (specDispatch ready base) checked (List.replicate checkCount .tau) checkEntry
  canonicalRun : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical
    (List.replicate canonCount .tau) canonEntry
  paired : HostFrame.Related.Paired (ReturnFrame.Extend older first second) checkEntry canonEntry

/-- A prefix can end before installation. Otherwise its original checked tail
provides the installed visitor's callback input and remaining boundary. -/
def InstalledCallbackSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (checkEntry canonEntry : Config (core3 grow) (HostState sig)) (checkCount : Nat)
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  actual.length < checkCount ∨ ∃ checkLabels canonLabels trailing reached peer,
    actual = List.replicate checkCount .tau ++ checkLabels ++ trailing ∧
    AllocatorCallbackPrefix profile ready base bindings older first second checkEntry canonEntry
      (some (checkLabels, canonLabels, peer)) (PayloadPrefix.visible checkLabels) reached ∧
    CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend older first second) reached peer trailing finish

/-- Compare an actual residual string program under the fixed live give
dispatcher. Each local segment may trap; each entered allocator can expose
any finite classified prefix. Only a pop of its marked occurrence enters a
smaller program. The terminal consumer can compare the real descriptor. -/
def LiveStringReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  let checkDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧ CoreGrowthSteps profile ready checkDispatch left labels lhs ∧
    CoreGrowthSteps profile ready canonDispatch right labels rhs ∧
    OccurrenceTransport profile ready base bindings left right labels labels lhs rhs ∧
    ∀ front, result = .ok front →
      RetainsActiveSlots profile ready checkDispatch left labels lhs ∧
      RetainsActiveSlots profile ready canonDispatch right labels rhs ∧
      match front with
      | .done pointer => finish pointer lhs rhs check canon
      | .call pointer oldSize alignment size rest _ =>
        let first := stringPlanResume cx rest checkNext
        let second := stringPlanResume cx rest canonNext
        let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
        let secondEntry := stringAllocatorEntry canonDispatch cx pointer oldSize alignment size rhs canon second
        PairedAllocatorInstall profile ready base bindings older first second lhs rhs firstEntry secondEntry 1 1 ∧
        ∀ {index seen reached}, AllocatorCallbackPrefix profile ready base bindings older first second firstEntry secondEntry index seen reached →
          ∃ checkLabels canonLabels reference mark,
            Steps profile ready checkDispatch lhs (.tau :: checkLabels) reached ∧
            Steps profile ready canonDispatch rhs (.tau :: canonLabels) reference ∧
            visible checkLabels = seen ∧ visible canonLabels = seen ∧
            HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
            Core3.Grows lhs.store.core reached.store.core ∧
            AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
            OccurrenceTransport profile ready base bindings lhs rhs (.tau :: checkLabels) (.tau :: canonLabels) reached reference [mark] ∧
            index.Matches checkLabels canonLabels reference ∧
            ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
              reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
              ∃ peer : Cursor (E := core3 grow) (HostState sig),
                let after := { reached with ctl := cursor.control (first (.nat value)) }
                let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
                RetainsActiveSlots profile ready checkDispatch lhs (.tau :: checkLabels ++ [.tau]) after ∧
                RetainsActiveSlots profile ready canonDispatch rhs (.tau :: canonLabels ++ [.tau]) referenceAfter ∧
                OccurrenceTransport profile ready base bindings lhs rhs (.tau :: checkLabels ++ [.tau])
                  (.tau :: canonLabels ++ [.tau]) after referenceAfter ∧
                LiveStringReplay profile ready base bindings older cx checkNext canonNext finish rest.length after referenceAfter cursor peer
termination_by length

/-- A string-plan traversal stops at the actual descriptor continuation, a
trap, a finite cut before the next local frontier, or an installed callback
whose exact mark has not popped with a pointer. -/
inductive StringSliceEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (describe : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (checked canonical : Config (core3 grow) (HostState sig))
    (trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) :
    List (Option ReturnFrame.Occurrence.Location) → Prop where
  | descriptor {pointer cursor peer} (reached : describe pointer checked canonical cursor peer) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | trap (left : checked.ctl = []) (right : canonical.ctl = []) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | localPrefix {reached remaining} (nonempty : remaining ≠ [])
      (localTail : Steps profile ready (specDispatch ready base) finish remaining reached) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | localChoice {leading taken suffix middle next} (split : trailing = leading ++ taken :: suffix)
      (choice : workerBranchLabel taken)
      (shared : Steps profile ready (specDispatch ready base) checked leading middle)
      (step : Step profile ready (specDispatch ready base) middle taken next)
      (tail : Steps profile ready (specDispatch ready base) next suffix finish) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | installPrefix (short : trailing.length < 1) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | collectionInstall (short : trailing.length < 3) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish []
  | collectionRange {reached remaining} (nonempty : remaining ≠ [])
      (localTail : Steps profile ready (specDispatch ready base) finish remaining reached) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish [some (.active 0 0)]
  | callback {checkEntry canonEntry checkLabels canonLabels mark first second}
      (tracked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkLabels canonLabels checked canonical mark)
      (paired : HostFrame.Related.Paired (ReturnFrame.Extend older first second) checked canonical)
      (ending : CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend older first second) checked canonical trailing finish)
      (notPopped : trailing = [] ∨ mark ≠ some (.active 0 0) ∨ ¬ ∃ (pointer : Nat)
        (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
        checked.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer))) :
      StringSliceEnd profile ready base bindings older describe checked canonical trailing finish [mark]

/-- The compared part of an actual checked string run. The residual is
always an execution from the reached checked state, not a new callback or
a canonical execution of the remainder. -/
def StringRunSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (describe : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels trailing reached peer marks,
    actual = checkLabels ++ trailing ∧
    PayloadPrefix.visible canonLabels = PayloadPrefix.visible checkLabels ∧
    OccurrenceTransport profile ready base bindings checked canonical checkLabels canonLabels reached peer marks ∧
    reached.store = peer.store ∧ Steps profile ready (specDispatch ready base) reached trailing finish ∧
    StringSliceEnd profile ready base bindings older describe reached peer trailing finish marks

/-- Two finite paths, compared at their reached stores and visible labels. -/
def ComparedPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels,
    Steps profile ready (specDispatch ready base) leftStart checkLabels left ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) rightStart canonLabels right ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- A compared prefix with a shared trajectory for every source coordinate.
The reached coordinate may differ from the source, or be absent on both sides. -/
def ComparedOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels,
    CoupledOccurrencePaths profile ready base bindings leftStart rightStart checkLabels canonLabels left right ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- One pair of reached traces witnesses both the visible prefix and the
transport of all enclosing marks. No temporary allocator mark remains open
at this cut. -/
def ComparedOccurrenceTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels,
    OccurrenceTransport profile ready base bindings leftStart rightStart checkLabels canonLabels left right ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- Cumulative all-location trails through the actual string plan. A finite
callback path need not reach a pop. Only the installed frame's actual return
continues the decreasing residual plan. -/
def LiveStringOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (leftStart rightStart : Config (core3 grow) (HostState sig))
    (finish : Nat → Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig)
    (leftBody : Config (core3 grow) (HostState sig) := left) (rightBody : Config (core3 grow) (HostState sig) := right) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧
    ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ visible labels) lhs rhs ∧
    (∃ checked canonical, OccurrenceTransport profile ready base bindings leftBody rightBody checked canonical lhs rhs) ∧
    match result with
    | .error _ => lhs.ctl = [] ∧ rhs.ctl = []
    | .ok (.done pointer) => finish pointer (seen ++ visible labels) lhs rhs check canon
    | .ok (.call pointer oldSize alignment size rest _) =>
      let first := stringPlanResume cx rest checkNext
      let second := stringPlanResume cx rest canonNext
      let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
      let secondEntry := stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base))
        cx pointer oldSize alignment size rhs canon second
      PairedAllocatorInstall profile ready base bindings older first second lhs rhs firstEntry secondEntry 1 1 ∧
      ∀ {index observed reached}, AllocatorCallbackPrefix profile ready base bindings older first second firstEntry secondEntry index observed reached →
        ∃ checkLabels canonLabels reference mark,
          AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
          HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
          ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ observed) reached reference ∧
          (∃ checked canonical, OccurrenceTransport profile ready base bindings leftBody rightBody checked canonical reached reference [mark]) ∧
          index.Matches checkLabels canonLabels reference ∧
          ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
            reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
            ∃ peer : Cursor (E := core3 grow) (HostState sig),
              let after := { reached with ctl := cursor.control (first (.nat value)) }
              let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
              ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ observed) after referenceAfter ∧
              LiveStringOccurrences profile ready base bindings older cx checkNext canonNext leftStart rightStart finish
                rest.length after referenceAfter cursor peer (seen ++ observed) leftBody rightBody
termination_by length

/-- A compared prefix with occurrence trails for active slots. The starting
offset accounts for older slots below an allocator frame that is popped. -/
def ComparedSlots (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) (offset : Nat := 0) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkLabels canonLabels,
    (∀ depth, Prefix profile ready (specDispatch ready base) leftStart (.active 0 (depth + offset)) checkLabels left (.active 0 depth)) ∧
    (∀ depth, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      rightStart (.active 0 (depth + offset)) canonLabels right (.active 0 depth)) ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen

/-- A finite allocation endpoint preserves the trajectory of every enclosing
active occurrence from traversal entry, not just the latest installed frame.
After installation an enclosing occurrence can move to a saved slot or be
lost; neither outcome is an allocator return. -/
def ComparedAllocatorPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) (offset : Nat := 0) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkLabels canonLabels,
    (∀ depth, ∃ reached,
      Trail profile ready (specDispatch ready base) leftStart (some (.active 0 (depth + offset))) checkLabels left reached ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
        rightStart (some (.active 0 (depth + offset))) canonLabels right reached) ∧
    PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧ left.store = right.store

/-- A continuation receives the visible history at its actual reached pair. -/
abbrev TrailFinish (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig

abbrev TrailFieldComparison (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Field → Nat → Nat → LinkedCallback.MemorySequence.CheckNext grow sig →
    LinkedCallback.MemorySequence.CanonNext grow sig → TrailFinish grow sig → TrailFinish grow sig

abbrev IssueProgram (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Issue → Session grow sig (Ret (core3 grow))

/-- All recursive wrappers either skip the suffix or add an issue index.
The sink receives the actual reached continuation, not a replay plan. -/
structure RefusalSink (grow : SingleThreaded.GrowOracle) (sig : Signature) where
  admits : IssueProgram grow sig → Prop
  nested : ∀ next, admits next → ∀ index, admits (fun issue => next (.nested index issue))
  exit : IssueProgram grow sig → Stored.Endpoints.RecordLower.Issue → Trace grow sig →
    Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
    PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop

def RefusalSink.ignore : RefusalSink grow sig := ⟨fun _ => True, fun _ _ _ => trivial, fun _ _ _ _ _ _ => True⟩

def RefusalSink.Covers (sink : RefusalSink grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) : Prop :=
  ∀ next, sink.admits next → ∀ issue seen left right check,
    left.ctl = check.control (next issue) → left.store = right.store →
    ComparedSlots profile ready base bindings start incoming seen left right offset → sink.exit next issue seen left right check

abbrev FlatTrailFinish (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  List FlatValue → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig

abbrev FlatFieldTrail (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Field → Nat → LinkedCallback.FlatSequenceCheckNext grow sig →
    LinkedCallback.FlatSequenceCanonNext grow sig → FlatTrailFinish grow sig → TrailFinish grow sig

/-- Local flat induction rule at a reached field. Only common success can
advance the sequence. Refusals use the checked error continuation; other
exits are represented by the field's own path relation. -/
def DerivesFlatFieldTrailWith (history : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId) (sink : RefusalSink grow sig)
    (path : FlatFieldTrail grow sig) (item : Stored.Endpoints.RecordLower.Field) : Prop :=
  open Stored.Endpoints.RecordLower in
  ∀ index checkNext canonNext finish before left right check canon,
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    history before left right →
    sink.admits (fun issue => checkNext (.error issue)) →
    left.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index .flat >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item .flat >>= canonNext) →
    (∀ words seen lhs rhs cursor peer, LinkedCallback.ChildFrameOver older lhs rhs cursor peer →
      Core3.Grows origin.core lhs.store.core → history seen lhs rhs →
      lhs.ctl = cursor.control (checkNext (.ok words)) → rhs.ctl = peer.control (canonNext words) →
      finish words seen lhs rhs cursor peer) →
    path item index checkNext canonNext finish before left right check canon


abbrev DerivesFlatFieldTrail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (destination : RecordDestination) (inst : InstId) (sink : RefusalSink grow sig)
    (path : FlatFieldTrail grow sig) (item : Stored.Endpoints.RecordLower.Field) : Prop :=
  DerivesFlatFieldTrailWith (fun seen left right => ComparedSlots profile ready base bindings start incoming seen left right offset)
    older origin destination inst sink path item

/-- Thread the actual flat words and cumulative occurrence history in order.
An error continuation does not run the remaining fields on either side. -/
def flatSequencePaths (destination : RecordDestination) (inst : InstId) (child : FlatFieldTrail grow sig)
    (checkNext : LinkedCallback.FlatSequenceCheckNext grow sig) (canonNext : LinkedCallback.FlatSequenceCanonNext grow sig)
    (finish : FlatTrailFinish grow sig) : List Stored.Endpoints.RecordLower.Field → Nat → List FlatValue → TrailFinish grow sig
  | [], _, leading => finish leading
  | item :: rest, index, leading =>
    open LinkedCallback in
    child item index
      (fun verdict => match verdict with
        | .error issue => checkNext (.error issue)
        | .ok words => flatSequenceChecked destination inst rest (index + 1) (leading ++ words) checkNext)
      (fun words => flatSequenceCanonical destination inst rest (leading ++ words) canonNext)
      (fun words => flatSequencePaths destination inst child checkNext canonNext finish rest (index + 1) (leading ++ words))

/-- A compiled field advances its sibling only at the actual success
continuation, carrying the chosen occurrence history to that reached pair. -/
def LiftsFieldPathsWith (history : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  ∀ item index address left right check canon checkNext canonNext finish visit before,
    field item index address left right check canon checkNext canonNext finish →
    history before left right →
    left.store = right.store →
    sink.admits (fun issue => checkNext (.error issue)) →
    (∀ seen lhs rhs cursor peer,
      history seen lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit seen lhs rhs cursor peer) →
    paths item index address checkNext canonNext visit before left right check canon

abbrev LiftsFieldPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  LiftsFieldPathsWith (fun seen left right => ComparedSlots profile ready base bindings start incoming seen left right offset)
    field paths sink

abbrev LiftsFieldOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig))
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  LiftsFieldPathsWith (ComparedOccurrencePaths profile ready base bindings start incoming) field paths sink

abbrev LiftsFieldTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig))
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  LiftsFieldPathsWith (ComparedOccurrenceTransport profile ready base bindings start incoming) field paths sink

/-- Follow the same slots, width reads and suffix programs as `ReplayBetween`,
but hand the cumulative visible history to the remaining sibling traversal. -/
def replayBetweenPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (mode : LinkedCallback.MemorySequence.Track) (destination : RecordDestination) (inst : InstId)
    (child : TrailFieldComparison grow sig) (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig)
    (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) (finish : TrailFinish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → TrailFinish grow sig
  | [], _, _, before, left, right, check, canon => finish before left right check canon
  | item :: rest, index, cursor, before, left, right, check, canon =>
    open LinkedCallback.MemorySequence in
    let slot := mode.slot destination.width item cursor
    let nextCheck := checkTail mode destination inst rest (index + 1) slot.2 checkNext
    let nextCanon := canonTail mode destination inst rest slot.2 canonNext
    let reference := focus mode destination inst item cursor right canon nextCanon
    ComparedOccurrencePaths profile ready base bindings left right [] left reference ∧
    child item index slot.1 nextCheck nextCanon
      (replayBetweenPaths profile ready base bindings mode destination inst child checkNext canonNext finish
        rest (index + 1) slot.2) before left reference check canon

/-- A cumulative view of the actual string plan. Compare a finite stopped
allocator prefix at its reached state; to continue, it must pop the marked
occurrence. Only a finished plan reaches the consumer. -/
def LiveStringPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (leftStart rightStart : Config (core3 grow) (HostState sig))
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) →
      Trace grow sig → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat := 0) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  let checkDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧ Steps profile ready checkDispatch left labels lhs ∧ Steps profile ready canonDispatch right labels rhs ∧
    match result with
    | .error reason => lhs.ctl = [] ∧ rhs.ctl = [] ∧
      ComparedPaths profile ready base bindings leftStart rightStart (seen ++ [.trap reason]) lhs rhs
    | .ok (.done pointer) => ComparedSlots profile ready base bindings leftStart rightStart seen lhs rhs offset ∧
      finish pointer lhs rhs check canon seen
    | .ok (.call pointer oldSize alignment size rest _) =>
      let first := stringPlanResume cx rest checkNext
      let second := stringPlanResume cx rest canonNext
      let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
      let secondEntry := stringAllocatorEntry canonDispatch cx pointer oldSize alignment size rhs canon second
      PairedAllocatorInstall profile ready base bindings older first second lhs rhs firstEntry secondEntry 1 1 ∧
      ∀ {index observed reached}, AllocatorCallbackPrefix profile ready base bindings older first second firstEntry secondEntry index observed reached →
        ∃ checkLabels canonLabels reference mark,
          AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
          HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
          ComparedAllocatorPaths profile ready base bindings leftStart rightStart (seen ++ observed) reached reference offset ∧
          index.Matches checkLabels canonLabels reference ∧
          ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
            reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
            ∃ peer : Cursor (E := core3 grow) (HostState sig),
              let after := { reached with ctl := cursor.control (first (.nat value)) }
              let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
              LiveStringPaths profile ready base bindings older cx checkNext canonNext leftStart rightStart finish
                rest.length after referenceAfter cursor peer (seen ++ observed) offset
termination_by length

/-- Validate the pointer from an actual marked return. The invalid branches
trap at the reached stores. The valid branch exposes the real checked live
verdict and the canonical child-entry program, before either executes children. -/
def CollectionRangeCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : ABI.Layout) (count pointer : Nat)
    (plan : List Stored.Endpoints.RecordLower.Object)
    (checkNext : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) : Prop :=
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  let traps := fun reason =>
    (∃ steps, Steps profile ready checkedDispatch checked (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg checked)) ∧
    (∃ steps, Steps profile ready canonDispatch canonical (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg canonical))
  ∃ canonCursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig), ∃ bytes,
    (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    LinkedCallback.ChildFrameOver older checked canonical cursor canonCursor ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then traps .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      (∃ trace, (∀ label ∈ trace, label = .tau) ∧ ReturnFrame.Occurrence.RetainsBelowTop profile ready checkedDispatch checked trace
        { checked with ctl := cursor.control (checkNext pointer (OwnedMemory.Claims.Record.prepare checked.store checked.host.writer plan)) }) ∧
      (∃ trace, (∀ label ∈ trace, label = .tau) ∧ ReturnFrame.Occurrence.RetainsBelowTop profile ready canonDispatch canonical trace
        { canonical with ctl := canonCursor.control (canonNext pointer) })
    else traps .outOfBounds

/-- Extend the exact enclosing trail across a collection's reached range
suffix. The input mark is the allocator's returned top occurrence, not an
arbitrary frame with an equal continuation. -/
def CollectionRangeTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checked canonical lhs rhs : Config (core3 grow) (HostState sig)) (observed : Trace grow sig) : Prop :=
  ∀ {leftStart rightStart checkTrace canonTrace},
    OccurrenceTransport profile ready base bindings leftStart rightStart checkTrace canonTrace checked canonical [some (.active 0 0)] →
    ∃ leftTail rightTail, OccurrenceTransport profile ready base bindings leftStart rightStart
      (checkTrace ++ leftTail) (canonTrace ++ rightTail) lhs rhs ∧
      PayloadPrefix.visible leftTail = observed ∧ PayloadPrefix.visible rightTail = observed ∧ lhs.store = rhs.store

/-- Cumulative paths through the real collection return. A fresh verdict
selects the checked continuation only; the canonical child program is still
pending. Range traps instead end both paths at the reached lockdown states. -/
def CollectionRangeOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (leftStart rightStart checked canonical : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : ABI.Layout) (count pointer : Nat)
    (plan : List Stored.Endpoints.RecordLower.Object)
    (checkNext : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) : Prop :=
  let traps := fun reason => ComparedOccurrencePaths profile ready base bindings leftStart rightStart
    (seen ++ [.trap reason]) (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) ∧
    CollectionRangeTransport profile ready base bindings checked canonical (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) [.trap reason]
  ∃ bytes, (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then traps .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
        let verdict := OwnedMemory.Claims.Record.prepare checked.store checked.host.writer plan
        let left := { checked with ctl := cursor.control (checkNext pointer verdict) }
        let right := { canonical with ctl := canon.control (canonNext pointer) }
        LinkedCallback.ChildFrameOver older left right cursor canon ∧
        (∃ labels, (∀ label ∈ labels, label = .tau) ∧
          RangeReturnTrails profile ready (specDispatch ready base) checked labels left) ∧
        (∃ labels, (∀ label ∈ labels, label = .tau) ∧
          RangeReturnTrails profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical labels right) ∧
        ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left right ∧
        CollectionRangeTransport profile ready base bindings checked canonical left right []
    else traps .outOfBounds

/-- Entry into the exact recursive bodies of a nested collection after its
marked allocator returns, range checks pass and a fresh reservation succeeds.
The all-location trail starts at this field's entry, while the active-slot
trail can start earlier. Both end at the same reached visitor states.
Memory-map placement keeps its allocation-time mode. -/
def LiveCollectionChildren (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming checked canonical : Config (core3 grow) (HostState sig)) (pointer bytes : Nat)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (observed localSeen : Trace grow sig)
    (visit : LinkedCallback.MemorySequence.Finish grow sig := fun _ _ _ _ => True)
    (leftStart : Config (core3 grow) (HostState sig) := start)
    (rightStart : Config (core3 grow) (HostState sig) := incoming) (offset : Nat := 0) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  ∃ left right canon,
    ComparedSlots profile ready base bindings leftStart rightStart observed left right offset ∧
    ComparedOccurrencePaths profile ready base bindings start incoming localSeen left right ∧
    ComparedOccurrenceTransport profile ready base bindings start incoming localSeen left right ∧
    LinkedCallback.ChildFrameOver older left right check canon ∧
    (core3 grow).memAddrType? left.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? left.store.core destination.memory = some bytes ∧
    pointer = alignTo pointer area.alignment ∧ pointer + entries.length * area.size ≤ bytes ∧
    Core3.Grows start.store.core left.store.core ∧
    left.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) ∧
    right.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) ∧
    CollectionRangeTransport profile ready base bindings checked canonical left right [] ∧
    visit left right check canon

/-- The unsuccessful branches of a marked range return, measured from the
recursive body origin and from the local field entry. Range traps run on both
sides. A fresh reservation failure follows only the checked issue continuation;
the canonical cursor is at its unexecuted child program. -/
def CollectionRangePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (observed : Trace grow sig) (offset : Nat)
    (destination : RecordDestination) (area : ABI.Layout) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (refuse : IssueProgram grow sig) (wrap : Stored.Endpoints.RecordLower.Issue → Stored.Endpoints.RecordLower.Issue)
    (children : Session grow sig (Ret (core3 grow)))
    (leftEntry rightEntry : Config (core3 grow) (HostState sig)) (localSeen : Trace grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  open Stored.Endpoints.RecordLower in
  let trap := fun reason => ComparedPaths profile ready base bindings leftStart rightStart (observed ++ [.trap reason])
    (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) ∧
    ComparedOccurrencePaths profile ready base bindings leftEntry rightEntry (localSeen ++ [.trap reason])
      (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) ∧
    ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry (localSeen ++ [.trap reason])
      (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical)
  ∃ bytes, (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + entries.length * area.size ≤ bytes then
      ∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
        ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
          let stopped := { checked with ctl := check.control (refuse (wrap issue)) }
          let reference := { canonical with ctl := canon.control children }
          checked.store = canonical.store ∧ ComparedSlots profile ready base bindings leftStart rightStart observed
            stopped reference offset ∧
          ComparedOccurrencePaths profile ready base bindings leftEntry rightEntry localSeen stopped reference ∧
          ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry localSeen stopped reference ∧
          sink.exit refuse (wrap issue) observed stopped reference check
    else trap .outOfBounds

/-- Finite callback paths for an actual dynamic child. A live mark at the
natural-pointer return is required to inspect the range. Failed range checks
trap, and a failed fresh reservation does not enter the children. The
all-location trails start before this field's preflight and install. -/
def LiveCollectionPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (visit : Nat → Nat → TrailFinish grow sig := fun _ _ _ _ _ _ _ => True)
    (leftStart : Config (core3 grow) (HostState sig) := start)
    (rightStart : Config (core3 grow) (HostState sig) := incoming) (leading : Trace grow sig := []) (offset : Nat := 0)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  let first := checkedCollectionResume destination inst entries area index output checkNext
  let second := canonicalCollectionResume destination inst entries area output canonNext mode
  let leftEntry := collectionEntry destination inst area entries.length (specDispatch ready base) start check first
  let rightEntry := collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
    incoming canon second
  PairedAllocatorInstall profile ready base bindings older first second start incoming leftEntry rightEntry 3 2 ∧
  ∀ {pathIndex seen finish}, AllocatorCallbackPrefix profile ready base bindings older first second leftEntry rightEntry pathIndex seen finish →
    ∃ checkLabels canonLabels reached mark,
      AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels finish reached mark ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      ComparedAllocatorPaths profile ready base bindings leftStart rightStart (leading ++ seen) finish reached offset ∧
      ComparedOccurrencePaths profile ready base bindings start incoming seen finish reached ∧
      OccurrenceTransport profile ready base bindings start incoming ([.tau, .tau, .tau] ++ checkLabels)
        ([.tau, .tau] ++ canonLabels) finish reached [mark] ∧
      pathIndex.Matches checkLabels canonLabels reached ∧
      ∀ pointer cursor, mark = some (.active 0 0) →
        finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
        CollectionRangeCut profile ready base bindings older finish reached cursor destination area entries.length pointer
          (Stored.Endpoints.RecordLower.Field.listObjects entries)
          (fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
          (fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) ∧
        CollectionRangePaths profile ready base bindings leftStart rightStart (leading ++ seen) offset destination area entries
          pointer finish reached cursor (fun issue => checkNext (.error issue)) (LinkedCallback.CollectionVisit.afterAllocation index)
          (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) start incoming seen sink ∧
        ∀ bytes, (core3 grow).memSize? finish.store.core destination.memory = some bytes →
          pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
          OwnedMemory.Claims.Record.prepare finish.store finish.host.writer (Field.listObjects entries) = .ok () →
          LiveCollectionChildren profile ready base bindings older destination inst type element entries index output checkNext
            canonNext start incoming finish reached pointer bytes cursor (leading ++ seen) seen
            (visit pointer bytes (leading ++ seen)) leftStart rightStart offset

/-- The live dry run before a nested allocation either reaches the typed
checked continuation alone or admits the finite allocator comparison. The
refusal leaves canonical at its original program, before any width read. -/
def LiveCollectionEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (visit : Nat → Nat → TrailFinish grow sig := fun _ _ _ _ _ _ _ => True)
    (leftStart : Config (core3 grow) (HostState sig) := start)
    (rightStart : Config (core3 grow) (HostState sig) := incoming) (leading : Trace grow sig := []) (offset : Nat := 0)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  open Stored.Endpoints.RecordLower in
  match OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) with
  | .error issue =>
    let refusal := match issue with
      | .preflight reason => Issue.field index (.beforeAllocation reason)
      | reason => Issue.nested index reason
    start.store = incoming.store ∧
    incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext) ∧
    let stopped := { start with ctl := check.control (checkNext (.error refusal)) }
    ComparedSlots profile ready base bindings leftStart rightStart leading stopped incoming offset ∧
    ComparedOccurrencePaths profile ready base bindings start incoming [] stopped incoming ∧
    OccurrenceTransport profile ready base bindings start incoming [.tau, .tau] [] stopped incoming ∧
    sink.exit (fun reason => checkNext (.error reason)) refusal leading stopped incoming check
  | .ok () => (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width →
    LiveCollectionPaths profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon visit leftStart rightStart leading offset sink

/-- A reached collection segment. The slot offset counts removed frames.
On checked refusal, the canonical program is the actual unexecuted suffix
at the reached stop, not necessarily the initial child-entry program. -/
def CollectionSegmentThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (offset : Nat)
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop)
    (next : Result → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (outcome : PayloadPrefix.Outcome Result)
    (checkLabels canonLabels : Trace grow sig) (left right : Config (core3 grow) (HostState sig)),
    Steps profile ready checkedDispatch checked checkLabels left ∧ Steps profile ready canonDispatch canonical canonLabels right ∧
    left.store = right.store ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    match outcome with
    | .trapped reason => left.ctl = [] ∧ right.ctl = [] ∧ ∃ leading, PayloadPrefix.visible canonLabels = leading ++ [.trap reason]
    | .returned value => LinkedCallback.ChildFrameOver older left right check canon ∧
        left.ctl = check.control (checkNext (.ok value)) ∧ right.ctl = canon.control (canonNext value) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready checkedDispatch checked (.active 0 (depth + offset))
          checkLabels left (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready canonDispatch canonical (.active 0 (depth + offset))
          canonLabels right (.active 0 depth)) ∧ next value left right canon
    | .refused issue => ∃ stop, stopsAt stop ∧
        left.ctl = check.control (checkNext (.error issue)) ∧ right.ctl = canon.control stop ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready checkedDispatch checked (.active 0 (depth + offset))
          checkLabels left (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready canonDispatch canonical (.active 0 (depth + offset))
          canonLabels right (.active 0 depth))

abbrev CollectionSegment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (offset : Nat)
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) (keep : CStore (core3 grow) → Prop := fun _ => True) : Prop :=
  CollectionSegmentThen profile ready base bindings older checked canonical check checkNext canonNext offset stopsAt
    (fun _ left _ _ => keep left.store)

/-- The specialization in which a failed fresh preparation stops before
any child executes. -/
abbrev CollectionReturn (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {Result : Type}
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (childEntry : Session grow sig (Ret (core3 grow))) : Prop :=
  CollectionSegment profile ready base bindings older checked canonical check checkNext canonNext 1 (· = childEntry)

/-- The unexecuted canonical list suffix at a reached nominal guard. The
address advances by the actual element stride, not by the number of writes. -/
def ElementStop (destination : RecordDestination) (inst : InstId) (entries : List Stored.Endpoints.RecordLower.Field)
    (stride ptr : Nat) (finish : Unit → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  ∃ leading remaining, entries = leading ++ remaining ∧ remaining ≠ [] ∧
    stop = (Stored.Endpoints.RecordLower.CanonicalTree.elements Limits.spec Quirks.none (destination.context inst)
      destination.width remaining .value stride (ptr + leading.length * stride) >>= finish)

/-- The nominal leaf schemas currently compared by the local collection rule. -/
inductive NominalElement : Stored.TypeOf → Prop where
  | own (resource : RtId) : NominalElement (.own resource)
  | future (element : Async.Element) : NominalElement (.future element)
  | stream (element : Async.Element) : NominalElement (.stream element)
  | context : NominalElement .errorContext

/-- The list depth is a property of the declared type, including empty
lists. It is independent of scheduler or allocator fuel. -/
inductive NominalListType : Nat → Stored.TypeOf → Prop where
  | leaf {type} : NominalElement type → NominalListType 0 type
  | list {depth element} : NominalListType depth element → NominalListType (depth + 1) (.list element)

/-- Visit an allocated list's actual element programs in order. The
continuation for a child admits the next sibling only on common success. -/
def liveElements (destination : RecordDestination) (inst : InstId) (stride : Nat)
    (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig
  | [], _, _, left, right, check, canon => finish left right check canon
  | item :: rest, index, pointer, left, right, check, canon =>
    open LinkedCallback.MemorySequence in
    child item index pointer left right check canon
      (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
      (canonTail (.elements stride) destination inst rest (pointer + stride) canonNext)
      (liveElements destination inst stride child checkNext canonNext finish rest (index + 1) (pointer + stride))

/-- Allocated elements already enter their canonical child at the placed
address. There is no additional per-element width read. -/
def liveElementsPaths (destination : RecordDestination) (inst : InstId) (stride : Nat)
    (child : TrailFieldComparison grow sig) (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig)
    (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) (finish : TrailFinish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → TrailFinish grow sig
  | [], _, _, before, left, right, check, canon => finish before left right check canon
  | item :: rest, index, pointer, before, left, right, check, canon =>
    open LinkedCallback.MemorySequence in
    child item index pointer
      (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
      (canonTail (.elements stride) destination inst rest (pointer + stride) canonNext)
      (liveElementsPaths destination inst stride child checkNext canonNext finish rest (index + 1) (pointer + stride))
      before left right check canon

/-- The real descriptor program executes only after every element returns.
The two paths share the descriptor result or canonical trap, not an assumed
rollback of either descriptor write. -/
def LiveValueCommit (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (finish : output.Result → LinkedCallback.MemorySequence.Finish grow sig) : LinkedCallback.MemorySequence.Finish grow sig :=
  fun left right check canon =>
  open PayloadPrefix in
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason output.Result) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest (fun value => checkNext (.ok value)) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result
    LocalLeafLabels result labels ∧
    CoreGrowthSteps profile ready (specDispatch ready base) left labels lhs ∧
    CoreGrowthSteps profile ready (specDispatch ready (LiveDispatch.host bindings base)) right labels rhs ∧
    OccurrenceTransport profile ready base bindings left right labels labels lhs rhs ∧
    ∀ value, result = .ok value →
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready base) left labels lhs ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base)) right labels rhs ∧
      finish value lhs rhs check canon

abbrev LiveListPublish := @LiveValueCommit

def liveListTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Nat) (output : Stored.Lower.Output) (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : LinkedCallback.MemorySequence.ValueFinish grow sig output) : Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig :=
  open ABI LinkedCallback.MemorySequence in
  fun pointer _ => liveElements destination inst (layout destination.width element).size compare
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext)
    (LiveListPublish profile ready base bindings output checkNext canonNext finish) entries 0 pointer

def liveListTailPaths (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (child : TrailFieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (publish : TrailFinish grow sig) : Nat → Nat → TrailFinish grow sig :=
  open ABI LinkedCallback.MemorySequence in
  fun pointer _ => liveElementsPaths destination inst (layout destination.width element).size child
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext) publish entries 0 pointer

/-- A decreasing comparison for nested list elements under the two live
dispatchers. Each allocation uses its own occurrence trail and rechecks
the actual reached writer before taking the child branch. -/
def liveNominalList (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Nat → LinkedCallback.MemorySequence.FieldComparison grow sig
  | 0 => fun item index address left right check canon checkNext canonNext finish =>
    LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index (.memory address) left right check canon
      checkNext canonNext (fun () => finish)
  | depth + 1 => fun item index address left right check canon checkNext canonNext finish =>
    open Stored.Endpoints.RecordLower in
    ∃ element entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext left right check canon
        (fun pointer bytes _ => liveListTail profile ready base bindings destination inst element entries index (.memory address)
          (liveNominalList profile ready base bindings older destination inst depth) checkNext canonNext (fun () => finish) pointer bytes)

/-- Enter the actual public bodies. The collection visitor sees the
children only at a valid return with a fresh successful reservation. -/
def LinkedCollectionBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (type element : Stored.TypeOf)
    (incoming : Config (core3 grow) (HostState sig))
    (visit : Config (core3 grow) (HostState sig) → List Stored.Endpoints.RecordLower.Field → Nat → Nat → TrailFinish grow sig) : Prop :=
  ∃ entries leading entered peer,
    site.field = .dynamic type element entries ∧ PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    entered.host = incoming.host ∧
    LiveCollectionPaths profile ready base bindings older site.destination site.inst type element entries 0
      route.output site.reply site.referenceReply site.checked entered site.cursor peer (visit entered entries)

abbrev LinkedNominalListBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (depth : Nat) (element : Stored.TypeOf)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedCollectionBody profile ready base bindings older site (.list element) element incoming (fun _ entries pointer bytes _ =>
    liveListTail profile ready base bindings site.destination site.inst element entries 0 route.output
      (liveNominalList profile ready base bindings older site.destination site.inst depth)
      site.reply site.referenceReply (fun _ _ _ _ _ => True) pointer bytes)

/-- Stop at fresh preparation or at a reached element; neither executes the
remaining canonical elements or publishes a descriptor. -/
def ListReturnStop (destination : RecordDestination) (inst : InstId) (entries : List Stored.Endpoints.RecordLower.Field)
    (area : ABI.Layout) (output : Stored.Lower.Output) (ptr : Nat)
    (finish : output.Result → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  stop = (PayloadPrefix.canonicalCollectionTail destination inst entries area output ptr >>= finish) ∨
  ElementStop destination inst entries area.size ptr
    (fun _ => Stored.Endpoints.ListLower.publish (destination.context inst) destination.width ptr entries.length output >>= finish) stop

def mapFieldPlacement (cx : LiftLowerContext (core3 grow))
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (next : AddrType → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  match mode with
  | .value => ptrType cx >>= next
  | .memoryMap width _ _ => next width

def mapValueProgram (destination : RecordDestination) (inst : InstId)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (value : Stored.Endpoints.RecordLower.Field) (afterKey : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  open Stored.Endpoints.RecordLower ABI in
  let cx := destination.context inst
  mapFieldPlacement cx mode fun width =>
    CanonicalTree.field Limits.spec Quirks.none cx destination.width value
      (.memory (alignTo afterKey (layout width value.type).alignment)) >>= finish

def mapKeyBody (destination : RecordDestination) (inst : InstId) (slot : Nat)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode) (key value : Stored.Endpoints.RecordLower.Field)
    (next : LinkedCallback.MemorySequence.CanonNext grow sig) (width : AddrType) : Session grow sig (Ret (core3 grow)) :=
  open Stored.Endpoints.RecordLower ABI in
  let area := layout width key.type
  let address := alignTo slot area.alignment
  CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width key (.memory address) >>=
    fun () => mapValueProgram destination inst mode value (address + area.size) next

/-- The key uses the reached map placement and runs before value placement.
If the value stops at its live guard, the stores in its comparison already
include the key write; the entry is not restarted at the key. -/
def LiveMapEntryThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (key value : Stored.Endpoints.RecordLower.Field) (index slot : Nat)
    (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) : LinkedCallback.MemorySequence.Finish grow sig :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence PayloadPrefix ReturnFrame.Occurrence in
  fun left right check canon =>
    let checked := specDispatch ready base
    let canonical := specDispatch ready (LiveDispatch.host bindings base)
    let cx := destination.context inst
    let keyArea := layout destination.width key.type
    let afterKey := alignTo slot keyArea.alignment + keyArea.size
    let valPtr := alignTo afterKey (layout destination.width value.type).alignment
    let report := aggregateNext index checkNext
    let valCheck := fun () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valPtr) >>= report
    let valCanon := fun () => mapValueProgram destination inst mode value afterKey canonNext
    let atKey := { right with ctl := canon.control (mapKeyBody destination inst slot mode key value canonNext destination.width) }
    ∃ keyRead, visible keyRead = [] ∧ (∀ place, Prefix profile ready canonical right place keyRead atKey place) ∧
    ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (checkLabels canonLabels : Trace grow sig),
      let lhs := localLeafEnd left left.host store check.thread check.frames check.rest valCheck result
      let rhs := localLeafEnd atKey right.host store canon.thread canon.frames canon.rest valCanon result
      Steps profile ready checked left checkLabels lhs ∧ LocalSteps profile ready canonical atKey canonLabels rhs ∧
      visible checkLabels = visible canonLabels ∧
      OccurrenceTransport profile ready base bindings left atKey checkLabels canonLabels lhs rhs ∧
      match result with
      | .error reason => ∃ leading, visible canonLabels = leading ++ [.trap reason]
      | .ok () =>
        let atValue := { rhs with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none cx destination.width value
          (.memory valPtr) >>= canonNext) }
        RetainsActiveSlots profile ready checked left checkLabels lhs ∧
        RetainsActiveSlots profile ready canonical atKey canonLabels rhs ∧
        ∃ valueRead, visible valueRead = [] ∧ (∀ place, Prefix profile ready canonical rhs place valueRead atValue place) ∧
          compare value 1 valPtr lhs atValue check canon report canonNext finish

abbrev MapEntryComparison (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Field → Stored.Endpoints.RecordLower.Field → Nat → Nat →
    LinkedCallback.MemorySequence.FieldComparison grow sig → LinkedCallback.MemorySequence.CheckNext grow sig →
    LinkedCallback.MemorySequence.CanonNext grow sig → LinkedCallback.MemorySequence.Finish grow sig →
    LinkedCallback.MemorySequence.Finish grow sig

def liveMapElementsWith (entry : MapEntryComparison grow sig)
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig
  | [], _, _, left, right, check, canon => finish left right check canon
  | item :: rest, index, pointer, left, right, check, canon =>
    open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let stride := (layout destination.width entryType).size
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      let keyField := Field.data (.prim key.toPrimitive) payload
      item = .aggregate entryType [keyField, value] ∧
      entry keyField value index pointer compare
        (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
        (fun () => CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width
          rest mode stride (pointer + stride) >>= canonNext)
        (liveMapElementsWith entry destination inst key element output compare checkNext canonNext finish
          rest (index + 1) (pointer + stride)) left right check canon

def liveMapTailWith (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (entry : MapEntryComparison grow sig)
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (compare : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : LinkedCallback.MemorySequence.ValueFinish grow sig output) : Nat → Nat → LinkedCallback.MemorySequence.Finish grow sig :=
  open LinkedCallback.MemorySequence in
  fun pointer _ => liveMapElementsWith entry destination inst key element output compare
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext)
    (LiveListPublish profile ready base bindings output checkNext canonNext finish) entries 0 pointer

abbrev liveMapTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output) :=
  liveMapTailWith profile ready base bindings
    (LiveMapEntryThen profile ready base bindings destination inst
      (Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width (.map key element) output))
    destination inst key element entries index output

abbrev LinkedMapListBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (key : WIT.KeyType) (depth : Nat) (element : Stored.TypeOf)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedCollectionBody profile ready base bindings older site (.map key element) (.record (ABI.mapEntryFields key element)) incoming
    (fun _ entries pointer bytes _ => liveMapTail profile ready base bindings site.destination site.inst key element entries 0 route.output
      (liveNominalList profile ready base bindings older site.destination site.inst depth)
      site.reply site.referenceReply (fun _ _ _ _ _ => True) pointer bytes)

/-- The current proof fragment, not the runtime support predicate. -/
inductive RecursiveCollectionType : Stored.TypeOf → Prop where
  | leaf {type} : NominalElement type → RecursiveCollectionType type
  | data {type} : PayloadPrefix.LocalDataType type → RecursiveCollectionType type
  | string : RecursiveCollectionType (.prim .string)
  | list {element} : RecursiveCollectionType element → RecursiveCollectionType (.list element)
  | fixed {element length} : RecursiveCollectionType element → RecursiveCollectionType (.fixedList element length)
  | map {key element} : RecursiveCollectionType element → RecursiveCollectionType (.map key element)
  | option {element} : RecursiveCollectionType element → RecursiveCollectionType (.option element)
  | result {success failure} : (∀ type, success = some type → RecursiveCollectionType type) →
      (∀ type, failure = some type → RecursiveCollectionType type) → RecursiveCollectionType (.result success failure)
  | variant {cases : List (String × Option Stored.TypeOf)} :
      (∀ name type, (name, some type) ∈ cases → RecursiveCollectionType type) → RecursiveCollectionType (.variant cases)
  | record {fields : List (String × Stored.TypeOf)} :
      (∀ name type, (name, type) ∈ fields → RecursiveCollectionType type) → RecursiveCollectionType (.record fields)
  | tuple {types : List Stored.TypeOf} :
      (∀ type, type ∈ types → RecursiveCollectionType type) → RecursiveCollectionType (.tuple types)

def CollectionRoot : Stored.TypeOf → Prop
  | .list _ | .map .. => True
  | _ => False

/-- Record either a canonical trap at the reached stores or a continuing
cursor pair with its original occurrences. Local completion does not choose
or run a later sibling. -/
def LocalPathsThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat)
    (finish : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig) : Prop :=
  (∃ reason leading lhs rhs,
    ComparedPaths profile ready base bindings start incoming (seen ++ (leading ++ [.trap reason])) lhs rhs ∧
    lhs.ctl = [] ∧ rhs.ctl = []) ∨
  (∃ more lhs rhs check canon,
    ComparedSlots profile ready base bindings start incoming (seen ++ more) lhs rhs offset ∧
    lhs.store = rhs.store ∧ finish (seen ++ more) lhs rhs check canon)

/-- A local field or flat coercion suffix with exact all-location paths from
its reached entry. These can be rebased even when an older occurrence is
saved or was lost before this cut. -/
def LocatedLocalPathsThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming left right : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat)
    (finish : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig) : Prop :=
  (∃ reason leading lhs rhs,
    ComparedPaths profile ready base bindings start incoming (seen ++ (leading ++ [.trap reason])) lhs rhs ∧
    ComparedOccurrencePaths profile ready base bindings left right (leading ++ [.trap reason]) lhs rhs ∧
    lhs.ctl = [] ∧ rhs.ctl = []) ∨
  (∃ more lhs rhs check canon,
    ComparedSlots profile ready base bindings start incoming (seen ++ more) lhs rhs offset ∧
    ComparedOccurrencePaths profile ready base bindings left right more lhs rhs ∧
    finish (seen ++ more) lhs rhs check canon)

/-- A typed live refusal advances only the checked guard; the canonical
cursor remains at the unexecuted field. Otherwise compare the reached stores
and continue only on success. -/
def HandlePathsThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat)
    (item : Stored.Endpoints.RecordLower.Field) (index : Nat)
    {Result : Type} (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (finish : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig)
    (left right : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (sink : RefusalSink grow sig := .ignore) : Prop :=
  (∃ issue, liveLeafPlan left.store left.host.writer index item = .error issue ∧
    let refused := { left with ctl := check.control (checkNext (.error issue)) }
    ComparedSlots profile ready base bindings start incoming seen refused right offset ∧
      ComparedOccurrencePaths profile ready base bindings left right [] refused right ∧
      sink.exit (fun reason => checkNext (.error reason)) issue seen refused right check) ∨
  LocatedLocalPathsThen profile ready base bindings start incoming left right seen offset finish

/-- A reached map key under the live dispatchers, from field placement
through the recursive string plan. Only completed plans reach the supplied
descriptor continuation. -/
def StringValueThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId)
    (key : LinkedCallback.StringField) (output : Stored.Lower.Output)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop) : Prop :=
  let cx := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
  let checked := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>=
    fun result => checkNext (.ok result)
  let canonical := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>= canonNext
  let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  ∃ checkLabels canonLabels,
    PayloadPrefix.visible checkLabels = [] ∧ PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base) left place checkLabels checkBody place) ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      right place canonLabels canonBody place) ∧
    LinkedCallback.ChildFrameOver older checkBody canonBody check canon ∧
    LiveStringReplay profile ready base bindings older cx checked canonical finish plan.steps.length checkBody canonBody check canon

abbrev StringKeyThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField) (address : Nat) :=
  StringValueThen profile ready base bindings older destination inst key (.memory address)

/-- The same string field along a cumulative occurrence path, including each
finite allocator prefix and the selected output continuation after actual return. -/
def StringValuePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField) (output : Stored.Lower.Output)
    (start incoming left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig) (seen : Trace grow sig) (offset : Nat) : Prop :=
  let cx := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
  let checked := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>=
    fun result => checkNext (.ok result)
  let canonical := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>= canonNext
  let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  LiveStringPaths profile ready base bindings older cx checked canonical start incoming
    (fun pointer lhs rhs check canon observed => finish pointer observed lhs rhs check canon)
    plan.steps.length checkBody canonBody check canon seen offset

/-- Follow every initial occurrence from the incoming field through the real
entry guards and the reached string plan, including finite allocator cuts. -/
def StringValueOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField) (output : Stored.Lower.Output)
    (start incoming left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig) (seen : Trace grow sig)
    (leftBody : Config (core3 grow) (HostState sig) := left) (rightBody : Config (core3 grow) (HostState sig) := right) : Prop :=
  let cx := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
  let checked := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>=
    fun result => checkNext (.ok result)
  let canonical := fun pointer => PayloadPrefix.stringPlanTail cx destination.width output plan pointer >>= canonNext
  let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  LiveStringOccurrences profile ready base bindings older cx checked canonical start incoming finish
    plan.steps.length checkBody canonBody check canon seen leftBody rightBody

abbrev StringKeyPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField) (address : Nat) :=
  StringValuePaths profile ready base bindings older destination inst key (.memory address)

def flatWordVisit (finish : FlatTrailFinish grow sig) : TrailFinish grow sig :=
  fun seen lhs rhs check canon => ∃ words, finish words seen lhs rhs check canon

def selectFlatPaths (paths : List (Stored.TypeOf × FlatFieldTrail grow sig)) : FlatFieldTrail grow sig :=
  fun item index checkNext canonNext finish before left right check canon =>
    ∃ child, (item.type, child) ∈ paths ∧ child item index checkNext canonNext finish before left right check canon

def flatAggregatePaths (destination : RecordDestination) (inst : InstId) (child : FlatFieldTrail grow sig) :
    FlatFieldTrail grow sig :=
  fun item index checkNext canonNext finish before left right check canon =>
    open Stored.Endpoints.RecordLower in
    ∃ children, LinkedCallback.flatChildren item = some children ∧
      flatSequencePaths destination inst child (fun verdict => checkNext (verdict.mapError (.nested index)))
        canonNext finish children 0 [] before left right check canon

def noFlatChild : FlatFieldTrail grow sig := fun _ _ _ _ _ _ _ _ _ _ => False

/-- The selected arm runs before the flat tag and coercion tail; the actual
checked error continuation skips that tail. -/
def flatSumPathsWith (tail : TrailFinish grow sig → TrailFinish grow sig) (width : AddrType) (type : Stored.TypeOf) (arms : List (Option Stored.TypeOf))
    (pick : Nat → FlatFieldTrail grow sig) : FlatFieldTrail grow sig :=
  fun item index checkNext canonNext finish before left right check canon =>
    open LinkedCallback ABI in
    ∃ tag selected, item = .sum type arms tag selected ∧
      match selected with
      | none => tail (flatWordVisit finish) before left right check canon
      | some child =>
        let haves := flatten width child.type
        pick tag child 0 (flatSumCheckNext width type arms.length tag index haves checkNext)
          (fun words => flatSumTail width type arms.length tag haves words >>= canonNext)
          (fun _ => tail (flatWordVisit finish))
          before left right check canon

abbrev TrailLeafType (type : Stored.TypeOf) : Prop :=
  NominalElement type ∨ PayloadPrefix.LocalDataType type ∨ type = .prim .string

abbrev flatSumPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (width : AddrType) (type : Stored.TypeOf) (arms : List (Option Stored.TypeOf))
    (pick : Nat → FlatFieldTrail grow sig) : FlatFieldTrail grow sig :=
  flatSumPathsWith (fun visit seen lhs rhs _ _ => LocatedLocalPathsThen profile ready base bindings start incoming lhs rhs seen offset visit)
    width type arms pick

/-- The trail comparison for the leaf cases of the compiled field visitor.
The corresponding theorem restricts this view to the certified leaf schemas. -/
def liveLeafPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig := .ignore) :
    Stored.TypeOf → TrailFieldComparison grow sig
  | .prim .string => fun item _ address checkNext canonNext finish before left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringKeyPaths profile ready base bindings older destination inst str address start incoming left right check canon
        checkNext canonNext (fun _ observed lhs rhs _ _ =>
          LocatedLocalPathsThen profile ready base bindings start incoming lhs rhs observed offset finish)
        before offset
  | .prim _ | .enum _ | .flags _ => fun _ _ _ _ _ finish before left right _ _ =>
    LocatedLocalPathsThen profile ready base bindings start incoming left right before offset finish
  | _ => fun item index _ checkNext _ finish before left right check _ =>
    HandlePathsThen profile ready base bindings start incoming before offset item index checkNext finish left right check sink

/-- At a closed leaf, retain the exact cumulative trap or feed the reached
return into the surrounding visitor. -/
def LocalOccurrenceThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (finish : TrailFinish grow sig) : Prop :=
  (∃ reason leading lhs rhs,
    ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ (leading ++ [.trap reason])) lhs rhs ∧
    lhs.ctl = [] ∧ rhs.ctl = []) ∨
  (∃ more lhs rhs check canon,
    ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ more) lhs rhs ∧
    finish (seen ++ more) lhs rhs check canon)

/-- A local operation either reaches a common trap or passes its augmented
history to the next actual continuation. -/
def LocalTransportThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig) (finish : TrailFinish grow sig) : Prop :=
  (∃ reason leading lhs rhs,
    ComparedOccurrenceTransport profile ready base bindings start incoming (seen ++ (leading ++ [.trap reason])) lhs rhs ∧
    lhs.ctl = [] ∧ rhs.ctl = []) ∨
  (∃ more lhs rhs check canon,
    ComparedOccurrenceTransport profile ready base bindings start incoming (seen ++ more) lhs rhs ∧
    finish (seen ++ more) lhs rhs check canon)

/-- A nominal guard can stop the checked field without running the
canonical leaf or any sibling. The occurrence history ends at that pair. -/
def HandleOccurrenceThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming left right : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (item : Stored.Endpoints.RecordLower.Field) (index : Nat) {Result : Type}
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (finish : TrailFinish grow sig) (sink : RefusalSink grow sig) : Prop :=
  (∃ issue, liveLeafPlan left.store left.host.writer index item = .error issue ∧
    let refused := { left with ctl := check.control (checkNext (.error issue)) }
    ComparedOccurrencePaths profile ready base bindings start incoming seen refused right ∧
    sink.exit (fun reason => checkNext (.error reason)) issue seen refused right check) ∨
  LocalOccurrenceThen profile ready base bindings start incoming seen finish

def RefusalSink.CoversOccurrences (sink : RefusalSink grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ next, sink.admits next → ∀ issue seen left right check,
    left.ctl = check.control (next issue) →
    ComparedOccurrencePaths profile ready base bindings start incoming seen left right → sink.exit next issue seen left right check

/-- The nominal guard's one-sided advance has a concrete checked trail
and an empty canonical trail. Success or a common trap uses the reached
spent writer, not the original authority. -/
def HandleTransportThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming left right : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (item : Stored.Endpoints.RecordLower.Field) (index : Nat) {Result : Type}
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (finish : TrailFinish grow sig) (sink : RefusalSink grow sig) : Prop :=
  (∃ issue, liveLeafPlan left.store left.host.writer index item = .error issue ∧
    let refused := { left with ctl := check.control (checkNext (.error issue)) }
    ComparedOccurrenceTransport profile ready base bindings start incoming seen refused right ∧
    sink.exit (fun reason => checkNext (.error reason)) issue seen refused right check) ∨
  LocalTransportThen profile ready base bindings start incoming seen finish

/-- The range branch of the actual marked return. Misalignment and bounds
traps retain the reached prefix. A fresh reservation failure stops canonical
before the child program, and only a successful reservation enters it. -/
def CollectionOccurrenceRangeThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (start incoming leftEntry rightEntry checked canonical : Config (core3 grow) (HostState sig)) (seen localSeen : Trace grow sig)
    (destination : RecordDestination) (area : ABI.Layout) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (refuse : IssueProgram grow sig) (wrap : Stored.Endpoints.RecordLower.Issue → Stored.Endpoints.RecordLower.Issue)
    (checkedChildren canonicalChildren : Session grow sig (Ret (core3 grow)))
    (visit : Nat → TrailFinish grow sig) (sink : RefusalSink grow sig) : Prop :=
  open Stored.Endpoints.RecordLower in
  let trap := fun reason => ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ [.trap reason])
    (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) ∧
    ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry (localSeen ++ [.trap reason])
      (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical)
  ∃ bytes, (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + entries.length * area.size ≤ bytes then
      (∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
        ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
          let stopped := { checked with ctl := check.control (refuse (wrap issue)) }
          let reference := { canonical with ctl := canon.control canonicalChildren }
          ComparedOccurrencePaths profile ready base bindings start incoming seen stopped reference ∧
          ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry localSeen stopped reference ∧
          sink.exit refuse (wrap issue) seen stopped reference check) ∧
      (OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .ok () →
        ∃ left right canon, ComparedOccurrencePaths profile ready base bindings start incoming seen left right ∧
          ComparedOccurrenceTransport profile ready base bindings leftEntry rightEntry localSeen left right ∧
          LinkedCallback.ChildFrameOver older left right check canon ∧
          (core3 grow).memAddrType? left.store.core destination.memory = some destination.width ∧
          (core3 grow).memSize? left.store.core destination.memory = some bytes ∧
          Core3.Grows origin.core left.store.core ∧
          left.ctl = check.control checkedChildren ∧ right.ctl = canon.control canonicalChildren ∧
          CollectionRangeTransport profile ready base bindings checked canonical left right [] ∧
          visit bytes seen left right check canon)
    else trap .outOfBounds

/-- Rebase an actual dynamic field at the reached occurrence coordinates.
Every classified finite allocator prefix is compared, but only the return
of the installed occurrence admits the range branch. -/
def LiveCollectionOccurrenceEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (start incoming left right : Config (core3 grow) (HostState sig)) (before : Trace grow sig)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (visit : Nat → Nat → TrailFinish grow sig) (sink : RefusalSink grow sig) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  match OwnedMemory.Claims.Record.prepare left.store left.host.writer (Field.listObjects entries) with
  | .error issue =>
    let refusal := match issue with
      | .preflight reason => Issue.field index (.beforeAllocation reason)
      | reason => Issue.nested index reason
    let stopped := { left with ctl := check.control (checkNext (.error refusal)) }
    ComparedOccurrencePaths profile ready base bindings start incoming before stopped right ∧
    OccurrenceTransport profile ready base bindings left right [.tau, .tau] [] stopped right ∧
    sink.exit (fun reason => checkNext (.error reason)) refusal before stopped right check
  | .ok () =>
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext mode
    let leftEntry := collectionEntry destination inst area entries.length (specDispatch ready base) left check first
    let rightEntry := collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
      right canon second
    (core3 grow).memAddrType? right.store.core destination.memory = some destination.width →
    PairedAllocatorInstall profile ready base bindings older first second left right leftEntry rightEntry 3 2 ∧
    ∀ {pathIndex seen finish}, AllocatorCallbackPrefix profile ready base bindings older first second leftEntry rightEntry pathIndex seen finish →
      ∃ checkLabels canonLabels reached mark,
        AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels finish reached mark ∧
        HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
        ComparedOccurrencePaths profile ready base bindings start incoming (before ++ seen) finish reached ∧
        OccurrenceTransport profile ready base bindings left right ([.tau, .tau, .tau] ++ checkLabels)
          ([.tau, .tau] ++ canonLabels) finish reached [mark] ∧
        pathIndex.Matches checkLabels canonLabels reached ∧
        ∀ pointer cursor, mark = some (.active 0 0) →
          finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
          CollectionOccurrenceRangeThen profile ready base bindings older left.store start incoming left right finish reached (before ++ seen) seen
            destination area entries pointer cursor (fun issue => checkNext (.error issue))
            (LinkedCallback.CollectionVisit.afterAllocation index)
            (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext)
            (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) (visit pointer) sink

/-- Actual memory leaves, including a string's reached descriptor write
and the nominal leaf's one-sided guard stop. -/
def leafOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) : Stored.TypeOf → TrailFieldComparison grow sig
  | .prim .string => fun item _ address checkNext canonNext finish seen left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValueOccurrencePaths profile ready base bindings older destination inst str (.memory address)
        start incoming left right check canon checkNext canonNext
        (fun _ observed _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming observed finish) seen
  | .prim _ | .enum _ | .flags _ => fun _ _ _ _ _ finish seen _ _ _ _ =>
    LocalOccurrenceThen profile ready base bindings start incoming seen finish
  | _ => fun item index _ checkNext _ finish seen left right check _ =>
    HandleOccurrenceThen profile ready base bindings start incoming left right seen item index check checkNext finish sink

abbrev StringKeyReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId)
    (key : LinkedCallback.StringField) (address : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  StringKeyThen profile ready base bindings older destination inst key address left right check canon checkNext canonNext
    (fun _ lhs rhs cursor peer =>
      LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧ Core3.Grows origin.core lhs.store.core ∧
      PayloadPrefix.StringLocalCutBetween profile ready (specDispatch ready base)
        (specDispatch ready (LiveDispatch.host bindings base)) lhs rhs cursor peer
        (fun result => checkNext (.ok result)) canonNext true)

/-- A string-key plan may suspend. Its actual descriptor writes must finish
before entering the value at the reached map slot. -/
def LiveStringMapEntryThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) : MapEntryComparison grow sig :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence PayloadPrefix ReturnFrame.Occurrence in
  fun field value index slot compare checkNext canonNext finish left right check canon =>
    ∃ key : LinkedCallback.StringField, field = key.field ∧
      let cx := destination.context inst
      let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
      let keyArea := layout destination.width key.field.type
      let address := alignTo slot keyArea.alignment
      let afterKey := address + keyArea.size
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := aggregateNext index checkNext
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valuePtr)) >>= report
      let canonical := fun () => mapValueProgram destination inst mode value afterKey canonNext
      StringKeyThen profile ready base bindings older destination inst key address left right check canon checked canonical
        (fun _ lhs rhs cursor peer =>
          let checkDispatch := specDispatch ready base
          let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
          ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (labels : Trace grow sig),
            let checkEnd := localLeafEnd lhs lhs.host store cursor.thread cursor.frames cursor.rest (fun res => checked (.ok res)) result
            let canonEnd := localLeafEnd rhs rhs.host store peer.thread peer.frames peer.rest canonical result
            LocalLeafLabels result labels ∧ CoreGrowthSteps profile ready checkDispatch lhs labels checkEnd ∧
            CoreGrowthSteps profile ready canonDispatch rhs labels canonEnd ∧
            OccurrenceTransport profile ready base bindings lhs rhs labels labels checkEnd canonEnd ∧
            match result with
            | .error _ => True
            | .ok () =>
              RetainsActiveSlots profile ready checkDispatch lhs labels checkEnd ∧
              RetainsActiveSlots profile ready canonDispatch rhs labels canonEnd ∧
              let atValue := { canonEnd with ctl := peer.control (CanonicalTree.field Limits.spec Quirks.none cx
                destination.width value (.memory valuePtr) >>= canonNext) }
              ∃ widthRead, visible widthRead = [] ∧ (∀ place, Prefix profile ready canonDispatch canonEnd place widthRead atValue place) ∧
                compare value 1 valuePtr checkEnd atValue cursor peer report canonNext finish)

/-- Track a string-key entry from the original caller pair through key
allocation, descriptor stores and the canonical width read. The value is
entered only after all three have completed. -/
def LiveStringMapEntryPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (start incoming : Config (core3 grow) (HostState sig))
    (seen : Trace grow sig) (offset : Nat) (field value : Stored.Endpoints.RecordLower.Field) (index slot : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (visit : Nat → TrailFinish grow sig)
    (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
  ∃ key : LinkedCallback.StringField, field = key.field ∧
    let cx := destination.context inst
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
    let keyArea := layout destination.width key.field.type
    let address := alignTo slot keyArea.alignment
    let afterKey := address + keyArea.size
    let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
    let report := aggregateNext index checkNext
    let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valuePtr)) >>= report
    let canonical := fun () => mapValueProgram destination inst mode value afterKey canonNext
    StringKeyPaths profile ready base bindings older destination inst key address start incoming left right check canon
      checked canonical (fun _ observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset (visit valuePtr))
      seen offset

def liveCollectionMapEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) : MapEntryComparison grow sig :=
  if key = .string then LiveStringMapEntryThen profile ready base bindings older destination inst element output
  else LiveMapEntryThen profile ready base bindings destination inst
    (Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput destination.width (.map key element) output)

abbrev MapEntryTrail (grow : SingleThreaded.GrowOracle) (sig : Signature) :=
  Stored.Endpoints.RecordLower.Field → Stored.Endpoints.RecordLower.Field → Nat → Nat →
    LinkedCallback.MemorySequence.CheckNext grow sig → LinkedCallback.MemorySequence.CanonNext grow sig →
    TrailFinish grow sig → TrailFinish grow sig

/-- The string-key plan, real descriptor stores, and live value placement.
The value visitor is entered only at the reached continuation. -/
def stringMapEntryOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (start incoming : Config (core3 grow) (HostState sig))
    (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
  fun field value index slot checkNext canonNext finish before left right check canon =>
    ∃ key : LinkedCallback.StringField, field = key.field ∧
      let cx := destination.context inst
      let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
      let keyArea := layout destination.width key.field.type
      let address := alignTo slot keyArea.alignment
      let afterKey := address + keyArea.size
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := aggregateNext index checkNext
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valuePtr)) >>= report
      let canonical := fun () => mapValueProgram destination inst mode value afterKey canonNext
      StringValueOccurrencePaths profile ready base bindings older destination inst key (.memory address)
        start incoming left right check canon checked canonical (fun _ observed _ _ _ _ =>
          LocalOccurrenceThen profile ready base bindings start incoming observed
            (child value 1 valuePtr report canonNext finish)) before

def mapEntryOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (key : WIT.KeyType) (element : Stored.TypeOf) (output : Stored.Lower.Output)
    (start incoming : Config (core3 grow) (HostState sig)) (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  if key = .string then
    stringMapEntryOccurrencePaths profile ready base bindings older destination inst element output start incoming child
  else
    open ABI LinkedCallback.MemorySequence in
    fun field value index slot checkNext canonNext finish before _ _ _ _ =>
      let keyArea := layout destination.width field.type
      let valuePtr := alignTo (alignTo slot keyArea.alignment + keyArea.size) (layout destination.width value.type).alignment
      LocalOccurrenceThen profile ready base bindings start incoming before
        (child value 1 valuePtr (aggregateNext index checkNext) canonNext finish)

/-- A reached string key transports all enclosing marks through its plan,
descriptor and placement. The value continuation is available only after
the descriptor and canonical placement have executed. -/
def StringMapEntryTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (start incoming : Config (core3 grow) (HostState sig))
    (visit : Nat → TrailFinish grow sig) (field value : Stored.Endpoints.RecordLower.Field) (index slot : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) :
    TrailFinish grow sig :=
  open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
  fun before left right check canon =>
    ∃ key : LinkedCallback.StringField, field = key.field ∧
      let cx := destination.context inst
      let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
      let keyArea := layout destination.width key.field.type
      let address := alignTo slot keyArea.alignment
      let afterKey := address + keyArea.size
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := aggregateNext index checkNext
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valuePtr)) >>= report
      let canonical := fun () => mapValueProgram destination inst mode value afterKey canonNext
      StringValueOccurrencePaths profile ready base bindings older destination inst key (.memory address)
        start incoming left right check canon checked canonical (fun _ _ _ _ cursor peer =>
          (∃ prior reason lhs rhs, ComparedOccurrenceTransport profile ready base bindings start incoming (prior ++ [.trap reason]) lhs rhs ∧
            lhs.ctl = [] ∧ rhs.ctl = []) ∨
          (∃ observed lhs rhs, ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs ∧
            visit valuePtr observed lhs rhs cursor peer)) before start incoming

def stringMapEntryTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (start incoming : Config (core3 grow) (HostState sig))
    (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  fun field value index slot checkNext canonNext finish =>
    StringMapEntryTransport profile ready base bindings older destination inst element output start incoming
      (fun pointer => child value 1 pointer (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
      field value index slot checkNext canonNext

/-- Select the reached key program before the recursive value. The
canonical entry mode is fixed by the allocation's output, not the value. -/
def mapEntryTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (key : WIT.KeyType) (element : Stored.TypeOf) (output : Stored.Lower.Output)
    (start incoming : Config (core3 grow) (HostState sig)) (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  if key = .string then
    stringMapEntryTransportPaths profile ready base bindings older destination inst element output start incoming child
  else
    open ABI LinkedCallback.MemorySequence in
    fun field value index slot checkNext canonNext finish before _ _ _ _ =>
      let keyArea := layout destination.width field.type
      let valuePtr := alignTo (alignTo slot keyArea.alignment + keyArea.size) (layout destination.width value.type).alignment
      LocalTransportThen profile ready base bindings start incoming before
        (child value 1 valuePtr (aggregateNext index checkNext) canonNext finish)

def liveMapEntryPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (key : WIT.KeyType) (element : Stored.TypeOf) (output : Stored.Lower.Output)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (child : TrailFieldComparison grow sig) : MapEntryTrail grow sig :=
  open ABI LinkedCallback.MemorySequence in
  fun field value index slot checkNext canonNext finish before left right check canon =>
    let after := fun addr => child value 1 addr (aggregateNext index checkNext) canonNext finish
    if key = .string then
      LiveStringMapEntryPaths profile ready base bindings older destination inst element output start incoming before offset
        field value index slot checkNext canonNext after left right check canon
    else
      let keyArea := layout destination.width field.type
      let valuePtr := alignTo (alignTo slot keyArea.alignment + keyArea.size) (layout destination.width value.type).alignment
      LocalPathsThen profile ready base bindings start incoming before offset (after valuePtr)

def liveMapElementsPaths (entry : MapEntryTrail grow sig)
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig)
    (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) (finish : TrailFinish grow sig) :
    List Stored.Endpoints.RecordLower.Field → Nat → Nat → TrailFinish grow sig
  | [], _, _, before, left, right, check, canon => finish before left right check canon
  | item :: rest, index, pointer, before, left, right, check, canon =>
    open Stored.Endpoints.RecordLower ABI LinkedCallback.MemorySequence in
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let stride := (layout destination.width entryType).size
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      let keyField := Field.data (.prim key.toPrimitive) payload
      item = .aggregate entryType [keyField, value] ∧
      entry keyField value index pointer
        (checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext)
        (fun () => CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width
          rest mode stride (pointer + stride) >>= canonNext)
        (liveMapElementsPaths entry destination inst key element output checkNext canonNext finish
          rest (index + 1) (pointer + stride)) before left right check canon

def liveMapTailPaths (entry : MapEntryTrail grow sig)
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (publish : TrailFinish grow sig) : Nat → Nat → TrailFinish grow sig :=
  open LinkedCallback.MemorySequence in
  fun pointer _ => liveMapElementsPaths entry destination inst key element output
    (publishChecked destination inst pointer entries.length index output checkNext)
    (publishCanonical destination inst pointer entries.length output canonNext) publish entries 0 pointer

def liveFixedPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : TrailFieldComparison grow sig)
    (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : TrailFinish grow sig) : TrailFinish grow sig :=
  open ABI LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  fun before left right check canon =>
    let stride := (layout destination.width element).size
    let reference := { right with ctl := canon.control (Track.canonical (.elements stride) destination inst entries address >>= canonNext) }
    (∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place [.tau] reference place) ∧
    liveElementsPaths destination inst stride child (aggregateNext index checkNext) canonNext finish entries 0 address
      before left reference check canon

/-- Both dispatchers run the actual local operations. Traps keep the stores
at the reached fault; only a successful field enters the continuation. -/
def LiveLocalFieldThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  let checked := specDispatch ready base
  let canonical := specDispatch ready (LiveDispatch.host bindings base)
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (lhsLabels rhsLabels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest (fun res => checkNext (.ok res)) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result
    Steps profile ready checked left lhsLabels lhs ∧ Steps profile ready canonical right rhsLabels rhs ∧
    PayloadPrefix.visible lhsLabels = PayloadPrefix.visible rhsLabels ∧
    OccurrenceTransport profile ready base bindings left right lhsLabels rhsLabels lhs rhs ∧
    match result with
    | .error reason => ∃ leading, PayloadPrefix.visible rhsLabels = leading ++ [.trap reason]
    | .ok () => ReturnFrame.Occurrence.RetainsActiveSlots profile ready checked left lhsLabels lhs ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready canonical right rhsLabels rhs ∧ finish lhs rhs check canon

/-- Write the reached discriminant before visiting the selected payload.
A trapped tag write never enters the child continuation. -/
def LiveSumThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (arms : List (Option Stored.TypeOf)) (selected : Option Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open PayloadPrefix LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  let addr := sumPayloadAddress destination.width arms address
  let checked := specDispatch ready base
  let canonical := specDispatch ready (LiveDispatch.host bindings base)
  let lhsNext := sumCheckedNext destination inst selected index addr checkNext
  let rhsNext := sumCanonicalNext destination inst selected addr canonNext
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (lhsLabels rhsLabels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest lhsNext result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest rhsNext result
    Steps profile ready checked left lhsLabels lhs ∧ Steps profile ready canonical right rhsLabels rhs ∧
    visible lhsLabels = visible rhsLabels ∧
    OccurrenceTransport profile ready base bindings left right lhsLabels rhsLabels lhs rhs ∧
    match result with
    | .error reason => ∃ leading, visible rhsLabels = leading ++ [.trap reason]
    | .ok () => RetainsActiveSlots profile ready checked left lhsLabels lhs ∧
      RetainsActiveSlots profile ready canonical right rhsLabels rhs ∧
      match selected with
      | none => finish lhs rhs check canon
      | some item => child item 0 addr lhs rhs check canon (aggregateNext index checkNext) canonNext finish

def LiveFixedThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open ABI Stored.Endpoints.RecordLower LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  let stride := (layout destination.width element).size
  let reference := { right with ctl := canon.control (Track.canonical (.elements stride) destination inst entries address >>= canonNext) }
  (∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place [.tau] reference place) ∧
    liveElements destination inst stride child (aggregateNext index checkNext) canonNext finish entries 0 address left reference check canon

def LiveAggregateThen (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : LinkedCallback.MemorySequence.FieldComparison grow sig)
    (items : List Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : LinkedCallback.MemorySequence.Finish grow sig) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  let entered := enterAggregate destination inst items index address left check checkNext
  (∀ place, Prefix profile ready (specDispatch ready base) left place [.tau] entered place) ∧
    ReplayBetween profile ready (specDispatch ready (LiveDispatch.host bindings base)) .fields destination inst child
      (aggregateNext index checkNext) canonNext finish items 0 address entered right check canon

def aggregateChild (comparisons : List (Stored.TypeOf × LinkedCallback.MemorySequence.FieldComparison grow sig)) :
    LinkedCallback.MemorySequence.FieldComparison grow sig :=
  fun item index address left right check canon checkNext canonNext finish =>
    ∃ compare, (item.type, compare) ∈ comparisons ∧ compare item index address left right check canon checkNext canonNext finish

/-- The actual aggregate bounds read precedes the field-by-field replay. -/
def liveAggregatePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (child : TrailFieldComparison grow sig)
    (items : List Stored.Endpoints.RecordLower.Field) (index address : Nat)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig)
    (finish : TrailFinish grow sig) : TrailFinish grow sig :=
  open LinkedCallback.MemorySequence ReturnFrame.Occurrence in
  fun before left right check canon =>
    let entered := enterAggregate destination inst items index address left check checkNext
    ComparedOccurrencePaths profile ready base bindings left right [] entered right ∧
      replayBetweenPaths profile ready base bindings .fields destination inst child
        (aggregateNext index checkNext) canonNext finish items 0 address before entered right check canon

def selectFieldPaths (paths : Stored.TypeOf → TrailFieldComparison grow sig) : TrailFieldComparison grow sig :=
  fun item => paths item.type item

/-- Leaf-only aggregates are one instance of the common sibling fold. -/
inductive TrailLeafAggregate : Stored.TypeOf → Prop where
  | record {fields} : (∀ field ∈ fields, TrailLeafType field.2) → TrailLeafAggregate (.record fields)
  | tuple {types} : (∀ type ∈ types, TrailLeafType type) → TrailLeafAggregate (.tuple types)

def aggregateFieldPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (destination : RecordDestination) (inst : InstId) (type : Stored.TypeOf)
    (paths : Stored.TypeOf → TrailFieldComparison grow sig) : TrailFieldComparison grow sig :=
  fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate type items ∧
      liveAggregatePaths profile ready base bindings destination inst (selectFieldPaths paths) items index address
        checkNext canonNext finish before left right check canon

mutual
/-- Recursion follows the declared type, not the number of reached allocator
returns. Each map selects the actual key rule before visiting its value. -/
def liveCollectionField (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    Stored.TypeOf → LinkedCallback.MemorySequence.FieldComparison grow sig
  | .list element => fun item index address left right check canon checkNext canonNext finish =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext left right check canon
        (fun pointer bytes _ => liveListTail profile ready base bindings destination inst element entries index (.memory address)
          (liveCollectionField profile ready base bindings older destination inst element) checkNext canonNext (fun () => finish) pointer bytes)
  | .map key element => fun item index address left right check canon checkNext canonNext finish =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    let output := Stored.Lower.Output.memory address
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        output checkNext canonNext left right check canon
        (fun pointer bytes _ => liveMapTailWith profile ready base bindings (liveCollectionMapEntry profile ready base bindings older destination inst key element output)
          destination inst key element entries index output
          (liveCollectionField profile ready base bindings older destination inst element) checkNext canonNext (fun () => finish) pointer bytes)
  | .fixedList element length => fun item index address left right check canon checkNext canonNext finish =>
    ∃ entries, item = .fixed element length entries ∧
      LiveFixedThen profile ready base bindings destination inst (liveCollectionField profile ready base bindings older destination inst element)
        element entries index address checkNext canonNext finish left right check canon
  | .option element => fun item index address left right check canon checkNext canonNext finish =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LiveSumThen profile ready base bindings destination inst (liveCollectionField profile ready base bindings older destination inst element)
        [none, some element] selected index address checkNext canonNext finish left right check canon
  | .result success failure => fun item index address left right check canon checkNext canonNext finish =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okCompare : LinkedCallback.MemorySequence.FieldComparison grow sig := match success with
        | some type => liveCollectionField profile ready base bindings older destination inst type
        | none => fun _ _ _ _ _ _ _ _ _ _ => False
      let errCompare : LinkedCallback.MemorySequence.FieldComparison grow sig := match failure with
        | some type => liveCollectionField profile ready base bindings older destination inst type
        | none => fun _ _ _ _ _ _ _ _ _ _ => False
      LiveSumThen profile ready base bindings destination inst (if tag = 0 then okCompare else errCompare)
        [success, failure] selected index address checkNext canonNext finish left right check canon
  | .variant cases => fun item index address left right check canon checkNext canonNext finish =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LiveSumThen profile ready base bindings destination inst
        (liveVariantArm profile ready base bindings older destination inst cases tag)
        (cases.map Prod.snd) selected index address checkNext canonNext finish left right check canon
  | .record fields => fun item index address left right check canon checkNext canonNext finish =>
    ∃ items, item = .aggregate (.record fields) items ∧
      LiveAggregateThen profile ready base bindings destination inst
        (aggregateChild (liveRecordFields profile ready base bindings older destination inst fields))
        items index address checkNext canonNext finish left right check canon
  | .tuple types => fun item index address left right check canon checkNext canonNext finish =>
    ∃ items, item = .aggregate (.tuple types) items ∧
      LiveAggregateThen profile ready base bindings destination inst
        (aggregateChild (liveTupleFields profile ready base bindings older destination inst types))
        items index address checkNext canonNext finish left right check canon
  | .prim .string => fun item _ address left right check canon checkNext canonNext finish =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringKeyThen profile ready base bindings older destination inst str address left right check canon checkNext canonNext
        (fun _ => LiveLocalFieldThen profile ready base bindings checkNext canonNext finish)
  | .prim _ | .enum _ | .flags _ => fun _ _ _ left right check canon checkNext canonNext finish =>
    LiveLocalFieldThen profile ready base bindings checkNext canonNext finish left right check canon
  | _ => fun item index address left right check canon checkNext canonNext finish =>
    LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index (.memory address) left right check canon
      checkNext canonNext (fun () => finish)
termination_by structural type => type

def liveVariantArm (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    List (String × Option Stored.TypeOf) → Nat → LinkedCallback.MemorySequence.FieldComparison grow sig
  | (_, some type) :: _, 0 => liveCollectionField profile ready base bindings older destination inst type
  | _ :: rest, tag + 1 => liveVariantArm profile ready base bindings older destination inst rest tag
  | _, _ => fun _ _ _ _ _ _ _ _ _ _ => False
termination_by structural cases => cases

def liveRecordFields (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × LinkedCallback.MemorySequence.FieldComparison grow sig)
  | [] => []
  | (_, type) :: rest => (type, liveCollectionField profile ready base bindings older destination inst type) ::
      liveRecordFields profile ready base bindings older destination inst rest
termination_by structural fields => fields

def liveTupleFields (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId) :
    List Stored.TypeOf → List (Stored.TypeOf × LinkedCallback.MemorySequence.FieldComparison grow sig)
  | [] => []
  | type :: rest => (type, liveCollectionField profile ready base bindings older destination inst type) ::
      liveTupleFields profile ready base bindings older destination inst rest
termination_by structural fields => fields
end

def selectPathField (paths : List (Stored.TypeOf × TrailFieldComparison grow sig)) : TrailFieldComparison grow sig :=
  fun item index address checkNext canonNext finish before left right check canon =>
    ∃ compare, (item.type, compare) ∈ paths ∧ compare item index address checkNext canonNext finish before left right check canon

mutual
/-- Thread one occurrence origin through the actual compiled shape. At a
dynamic child preserve its marked allocator cut; only entered descendants
may proceed to their descriptor and the next sibling. -/
def liveRecursivePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    Stored.TypeOf → TrailFieldComparison grow sig
  | .list element => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext left right check canon
        (liveListTailPaths destination inst element entries index (.memory address)
          (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element)
          checkNext canonNext (fun observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset finish))
        start incoming before offset sink
  | .map key element => fun item index address checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    let output := Stored.Lower.Output.memory address
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        output checkNext canonNext left right check canon
        (liveMapTailPaths (liveMapEntryPaths profile ready base bindings older destination inst key element output start incoming offset
          (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element))
          destination inst key element entries index output checkNext canonNext
          (fun observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset finish))
        start incoming before offset sink
  | .fixedList element length => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .fixed element length entries ∧
      liveFixedPaths profile ready base bindings destination inst
        (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element) element entries index address
        checkNext canonNext finish before left right check canon
  | .option element => fun item index address checkNext canonNext finish before left right _ _ =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LocatedLocalPathsThen profile ready base bindings start incoming left right before offset
        (match selected with
        | none => finish
        | some arm => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [none, some element] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .result success failure => fun item index address checkNext canonNext finish before left right _ _ =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okPaths : TrailFieldComparison grow sig := match success with
        | some type => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      let errorPaths : TrailFieldComparison grow sig := match failure with
        | some type => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      LocatedLocalPathsThen profile ready base bindings start incoming left right before offset
        (match selected with
        | none => finish
        | some arm => (if tag = 0 then okPaths else errorPaths) arm 0 (PayloadPrefix.sumPayloadAddress destination.width [success, failure] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .variant cases => fun item index address checkNext canonNext finish before left right _ _ =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LocatedLocalPathsThen profile ready base bindings start incoming left right before offset
        (match selected with
        | none => finish
        | some arm => liveVariantPaths profile ready base bindings older destination inst start incoming offset sink cases tag arm 0
            (PayloadPrefix.sumPayloadAddress destination.width (cases.map Prod.snd) address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .record fields => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.record fields) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (liveRecordTrails profile ready base bindings older destination inst start incoming offset sink fields))
        items index address checkNext canonNext finish before left right check canon
  | .tuple types => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.tuple types) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (liveTupleTrails profile ready base bindings older destination inst start incoming offset sink types))
        items index address checkNext canonNext finish before left right check canon
  | type => liveLeafPaths profile ready base bindings older destination inst start incoming offset sink type
termination_by structural type => type

def liveVariantPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → TrailFieldComparison grow sig
  | (_, some type) :: _, 0 => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type
  | _ :: rest, tag + 1 => liveVariantPaths profile ready base bindings older destination inst start incoming offset sink rest tag
  | _, _ => fun _ _ _ _ _ _ _ _ _ _ _ => False
termination_by structural cases => cases

def liveRecordTrails (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | (_, type) :: rest => (type, liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type) ::
      liveRecordTrails profile ready base bindings older destination inst start incoming offset sink rest
termination_by structural fields => fields

def liveTupleTrails (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | type :: rest => (type, liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type) ::
      liveTupleTrails profile ready base bindings older destination inst start incoming offset sink rest
termination_by structural types => types
end

/-- The enclosing-mark invariant covers the compiled memory visitor's
recursive fragment; it is not a runtime admission predicate. -/
abbrev RecursiveAllocatingTransportType := RecursiveCollectionType

mutual
/-- Follow each reached child of the compiled memory visitor, carrying the
enclosing marks through the real placement, allocator and continuation. -/
def recursiveAllocatingTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) : Stored.TypeOf → TrailFieldComparison grow sig
  | .list element => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext start incoming left right before check canon
        (liveListTailPaths destination inst element entries index (.memory address)
          (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element) checkNext canonNext
          (fun observed _ _ _ _ => LocalTransportThen profile ready base bindings start incoming observed finish)) sink
  | .map key element => fun item index address checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    let output := Stored.Lower.Output.memory address
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        output checkNext canonNext start incoming left right before check canon
        (liveMapTailPaths (mapEntryTransportPaths profile ready base bindings older destination inst key element output start incoming
          (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element))
          destination inst key element entries index output checkNext canonNext
          (fun observed _ _ _ _ => LocalTransportThen profile ready base bindings start incoming observed finish)) sink
  | .fixedList element length => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .fixed element length entries ∧
      liveFixedPaths profile ready base bindings destination inst
        (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element)
        element entries index address checkNext canonNext finish before left right check canon
  | .option element => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LocalTransportThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [none, some element] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .result success failure => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okPaths : TrailFieldComparison grow sig := match success with
        | some type => recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      let errorPaths : TrailFieldComparison grow sig := match failure with
        | some type => recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      LocalTransportThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => (if tag = 0 then okPaths else errorPaths) arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [success, failure] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .variant cases => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LocalTransportThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => recursiveVariantTransportPaths profile ready base bindings older destination inst start incoming sink cases tag arm 0
            (PayloadPrefix.sumPayloadAddress destination.width (cases.map Prod.snd) address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .record fields => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.record fields) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (recursiveRecordTransportPaths profile ready base bindings older destination inst start incoming sink fields))
        items index address checkNext canonNext finish before left right check canon
  | .tuple types => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.tuple types) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (recursiveTupleTransportPaths profile ready base bindings older destination inst start incoming sink types))
        items index address checkNext canonNext finish before left right check canon
  | .prim .string => fun item _ address checkNext canonNext finish seen left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValueOccurrencePaths profile ready base bindings older destination inst str (.memory address)
        start incoming left right check canon checkNext canonNext
        (fun _ _ _ _ _ _ => ∃ seen, LocalTransportThen profile ready base bindings start incoming seen finish) seen start incoming
  | .prim _ | .enum _ | .flags _ => fun _ _ _ _ _ finish seen _ _ _ _ =>
    LocalTransportThen profile ready base bindings start incoming seen finish
  | _ => fun item index _ checkNext _ finish seen left right check _ =>
    HandleTransportThen profile ready base bindings start incoming left right seen item index check checkNext finish sink
termination_by structural type => type

def recursiveVariantTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → TrailFieldComparison grow sig
  | (_, some type) :: _, 0 => recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type
  | _ :: rest, tag + 1 => recursiveVariantTransportPaths profile ready base bindings older destination inst start incoming sink rest tag
  | _, _ => fun _ _ _ _ _ _ _ _ _ _ _ => False
termination_by structural cases => cases

def recursiveRecordTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | (_, type) :: rest => (type, recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type) ::
      recursiveRecordTransportPaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural fields => fields

def recursiveTupleTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | type :: rest => (type, recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type) ::
      recursiveTupleTransportPaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural types => types
end

/-- The cumulative memory fold covers the same fragment as the compiled
recursive visitor, with no additional runtime admission condition. -/
abbrev StructuralMemoryOccurrenceType := RecursiveCollectionType

mutual
def structuralMemoryOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    Stored.TypeOf → TrailFieldComparison grow sig
  | .list element => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index
        (.memory address) checkNext canonNext start incoming left right before check canon
        (liveListTailPaths destination inst element entries index (.memory address)
          (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element)
          checkNext canonNext (fun observed _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming observed finish)) sink
  | .map key element => fun item index address checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    let output := Stored.Lower.Output.memory address
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        output checkNext canonNext start incoming left right before check canon
        (liveMapTailPaths (mapEntryOccurrencePaths profile ready base bindings older destination inst key element output start incoming
          (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element))
          destination inst key element entries index output checkNext canonNext
          (fun observed _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming observed finish)) sink
  | .fixedList element length => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .fixed element length entries ∧
      liveFixedPaths profile ready base bindings destination inst
        (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element) element entries index address
        checkNext canonNext finish before left right check canon
  | .option element => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LocalOccurrenceThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [none, some element] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .result success failure => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okPaths : TrailFieldComparison grow sig := match success with
        | some type => structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      let errorPaths : TrailFieldComparison grow sig := match failure with
        | some type => structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      LocalOccurrenceThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => (if tag = 0 then okPaths else errorPaths) arm 0 (PayloadPrefix.sumPayloadAddress destination.width [success, failure] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .variant cases => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LocalOccurrenceThen profile ready base bindings start incoming before
        (match selected with
        | none => finish
        | some arm => structuralVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink cases tag arm 0
            (PayloadPrefix.sumPayloadAddress destination.width (cases.map Prod.snd) address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .record fields => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.record fields) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (structuralRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink fields))
        items index address checkNext canonNext finish before left right check canon
  | .tuple types => fun item index address checkNext canonNext finish before left right check canon =>
    ∃ items, item = .aggregate (.tuple types) items ∧
      liveAggregatePaths profile ready base bindings destination inst
        (selectPathField (structuralTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink types))
        items index address checkNext canonNext finish before left right check canon
  | type => leafOccurrencePaths profile ready base bindings older destination inst start incoming sink type
termination_by structural type => type

def structuralVariantOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → TrailFieldComparison grow sig
  | (_, some type) :: _, 0 => structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type
  | _ :: rest, tag + 1 => structuralVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink rest tag
  | _, _ => fun _ _ _ _ _ _ _ _ _ _ _ => False
termination_by structural cases => cases

def structuralRecordOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | (_, type) :: rest => (type, structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural fields => fields

def structuralTupleOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × TrailFieldComparison grow sig)
  | [] => []
  | type :: rest => (type, structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural types => types
end

mutual
def liveFlatPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    Stored.TypeOf → FlatFieldTrail grow sig
  | .prim .string => fun item _ checkNext canonNext finish before left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValuePaths profile ready base bindings older destination inst str .flat start incoming left right check canon checkNext canonNext
        (fun _ observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset (flatWordVisit finish))
        before offset
  | .list element => fun item index checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index
        .flat checkNext canonNext left right check canon
        (liveListTailPaths destination inst element entries index .flat
          (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element)
          checkNext canonNext
          (fun seen _ _ _ _ => LocalPathsThen profile ready base bindings start incoming seen offset (flatWordVisit finish)))
        start incoming before offset sink
  | .map key element => fun item index checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionEntry profile ready base bindings older destination inst (.map key element) entryType entries index
        .flat checkNext canonNext left right check canon
        (liveMapTailPaths (liveMapEntryPaths profile ready base bindings older destination inst key element .flat start incoming offset
          (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element))
          destination inst key element entries index .flat checkNext canonNext
          (fun seen _ _ _ _ => LocalPathsThen profile ready base bindings start incoming seen offset (flatWordVisit finish)))
        start incoming before offset sink
  | .fixedList element _ => flatAggregatePaths destination inst
      (liveFlatPaths profile ready base bindings older destination inst start incoming offset sink element)
  | .option element => flatSumPaths profile ready base bindings start incoming offset destination.width
      (.option element) [none, some element]
      (fun _ => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink element)
  | .result success failure =>
    let first := match success with
      | none => noFlatChild
      | some type => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type
    let second := match failure with
      | none => noFlatChild
      | some type => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type
    flatSumPaths profile ready base bindings start incoming offset destination.width (.result success failure) [success, failure]
      (fun tag => if tag = 0 then first else second)
  | .variant cases => flatSumPaths profile ready base bindings start incoming offset destination.width
      (.variant cases) (cases.map Prod.snd) (liveFlatVariantPaths profile ready base bindings older destination inst start incoming offset sink cases)
  | .record fields => flatAggregatePaths destination inst
      (selectFlatPaths (liveFlatRecordPaths profile ready base bindings older destination inst start incoming offset sink fields))
  | .tuple types => flatAggregatePaths destination inst
      (selectFlatPaths (liveFlatTuplePaths profile ready base bindings older destination inst start incoming offset sink types))
  | .own _ | .future _ | .stream _ | .errorContext => fun item index checkNext _ finish before left right check _ =>
    HandlePathsThen profile ready base bindings start incoming before offset item index checkNext (flatWordVisit finish) left right check sink
  | _ => fun _ _ _ _ finish before left right _ _ =>
    LocatedLocalPathsThen profile ready base bindings start incoming left right before offset (flatWordVisit finish)
termination_by structural type => type

def liveFlatRecordPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | (_, type) :: rest =>
    (type, liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type) ::
      liveFlatRecordPaths profile ready base bindings older destination inst start incoming offset sink rest
termination_by structural fields => fields

def liveFlatTuplePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | type :: rest =>
    (type, liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type) ::
      liveFlatTuplePaths profile ready base bindings older destination inst start incoming offset sink rest
termination_by structural types => types

def liveFlatVariantPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → FlatFieldTrail grow sig
  | [], _ | (_, none) :: _, 0 => noFlatChild
  | (_, some type) :: _, 0 => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type
  | _ :: rest, tag + 1 => liveFlatVariantPaths profile ready base bindings older destination inst start incoming offset sink rest tag
termination_by structural cases => cases
end

mutual
def structuralFlatOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    Stored.TypeOf → FlatFieldTrail grow sig
  | .prim .string => fun item _ checkNext canonNext finish before left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValueOccurrencePaths profile ready base bindings older destination inst str .flat start incoming left right check canon checkNext canonNext
        (fun _ seen _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming seen (flatWordVisit finish)) before
  | .list element => fun item index checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index .flat
        checkNext canonNext start incoming left right before check canon
        (liveListTailPaths destination inst element entries index .flat
          (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element)
          checkNext canonNext (fun seen _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming seen (flatWordVisit finish))) sink
  | .map key element => fun item index checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element) entryType entries index .flat
        checkNext canonNext start incoming left right before check canon
        (liveMapTailPaths (mapEntryOccurrencePaths profile ready base bindings older destination inst key element .flat start incoming
          (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink element))
          destination inst key element entries index .flat checkNext canonNext
          (fun seen _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming seen (flatWordVisit finish))) sink
  | .fixedList element _ => flatAggregatePaths destination inst
      (structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink element)
  | .option element => flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalOccurrenceThen profile ready base bindings start incoming seen visit) destination.width
      (.option element) [none, some element]
      (fun _ => structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink element)
  | .result success failure =>
    let first := match success with
      | none => noFlatChild
      | some type => structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type
    let second := match failure with
      | none => noFlatChild
      | some type => structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type
    flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalOccurrenceThen profile ready base bindings start incoming seen visit) destination.width (.result success failure) [success, failure]
      (fun tag => if tag = 0 then first else second)
  | .variant cases => flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalOccurrenceThen profile ready base bindings start incoming seen visit) destination.width
      (.variant cases) (cases.map Prod.snd) (structuralFlatVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink cases)
  | .record fields => flatAggregatePaths destination inst
      (selectFlatPaths (structuralFlatRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink fields))
  | .tuple types => flatAggregatePaths destination inst
      (selectFlatPaths (structuralFlatTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink types))
  | .own _ | .future _ | .stream _ | .errorContext => fun item index checkNext _ finish before left right check _ =>
    HandleOccurrenceThen profile ready base bindings start incoming left right before item index check checkNext (flatWordVisit finish) sink
  | _ => fun _ _ _ _ finish before _ _ _ _ =>
    LocalOccurrenceThen profile ready base bindings start incoming before (flatWordVisit finish)
termination_by structural type => type

def structuralFlatRecordOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | (_, type) :: rest =>
    (type, structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralFlatRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural fields => fields

def structuralFlatTupleOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | type :: rest =>
    (type, structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralFlatTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural types => types

def structuralFlatVariantOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → FlatFieldTrail grow sig
  | [], _ | (_, none) :: _, 0 => noFlatChild
  | (_, some type) :: _, 0 => structuralFlatOccurrencePaths profile ready base bindings older destination inst start incoming sink type
  | _ :: rest, tag + 1 => structuralFlatVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink rest tag
termination_by structural cases => cases
end

mutual
def structuralFlatTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    Stored.TypeOf → FlatFieldTrail grow sig
  | .prim .string => fun item _ checkNext canonNext finish before left right check canon =>
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringValueOccurrencePaths profile ready base bindings older destination inst str .flat start incoming left right check canon checkNext canonNext
        (fun _ _ _ _ _ _ => ∃ seen, LocalTransportThen profile ready base bindings start incoming seen (flatWordVisit finish)) before start incoming
  | .list element => fun item index checkNext canonNext finish before left right check canon =>
    ∃ entries, item = .dynamic (.list element) element entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index .flat
        checkNext canonNext start incoming left right before check canon
        (liveListTailPaths destination inst element entries index .flat
          (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element)
          checkNext canonNext (fun seen _ _ _ _ => LocalTransportThen profile ready base bindings start incoming seen (flatWordVisit finish))) sink
  | .map key element => fun item index checkNext canonNext finish before left right check canon =>
    let entryType : Stored.TypeOf := .record (ABI.mapEntryFields key element)
    ∃ entries, item = .dynamic (.map key element) entryType entries ∧
      LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element) entryType entries index .flat
        checkNext canonNext start incoming left right before check canon
        (liveMapTailPaths (mapEntryTransportPaths profile ready base bindings older destination inst key element .flat start incoming
          (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink element))
          destination inst key element entries index .flat checkNext canonNext
          (fun seen _ _ _ _ => LocalTransportThen profile ready base bindings start incoming seen (flatWordVisit finish))) sink
  | .fixedList element _ => flatAggregatePaths destination inst
      (structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink element)
  | .option element => flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalTransportThen profile ready base bindings start incoming seen visit) destination.width
      (.option element) [none, some element]
      (fun _ => structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink element)
  | .result success failure =>
    let first := match success with
      | none => noFlatChild
      | some type => structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type
    let second := match failure with
      | none => noFlatChild
      | some type => structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type
    flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalTransportThen profile ready base bindings start incoming seen visit) destination.width (.result success failure) [success, failure]
      (fun tag => if tag = 0 then first else second)
  | .variant cases => flatSumPathsWith (fun visit seen _ _ _ _ =>
      LocalTransportThen profile ready base bindings start incoming seen visit) destination.width
      (.variant cases) (cases.map Prod.snd) (structuralFlatVariantTransportPaths profile ready base bindings older destination inst start incoming sink cases)
  | .record fields => flatAggregatePaths destination inst
      (selectFlatPaths (structuralFlatRecordTransportPaths profile ready base bindings older destination inst start incoming sink fields))
  | .tuple types => flatAggregatePaths destination inst
      (selectFlatPaths (structuralFlatTupleTransportPaths profile ready base bindings older destination inst start incoming sink types))
  | .own _ | .future _ | .stream _ | .errorContext => fun item index checkNext _ finish before left right check _ =>
    HandleTransportThen profile ready base bindings start incoming left right before item index check checkNext (flatWordVisit finish) sink
  | _ => fun _ _ _ _ finish before _ _ _ _ =>
    LocalTransportThen profile ready base bindings start incoming before (flatWordVisit finish)
termination_by structural type => type

def structuralFlatRecordTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Stored.TypeOf) → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | (_, type) :: rest =>
    (type, structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralFlatRecordTransportPaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural fields => fields

def structuralFlatTupleTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List Stored.TypeOf → List (Stored.TypeOf × FlatFieldTrail grow sig)
  | [] => []
  | type :: rest =>
    (type, structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type) ::
      structuralFlatTupleTransportPaths profile ready base bindings older destination inst start incoming sink rest
termination_by structural types => types

def structuralFlatVariantTransportPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (start incoming : Config (core3 grow) (HostState sig)) (sink : RefusalSink grow sig) :
    List (String × Option Stored.TypeOf) → Nat → FlatFieldTrail grow sig
  | [], _ | (_, none) :: _, 0 => noFlatChild
  | (_, some type) :: _, 0 => structuralFlatTransportPaths profile ready base bindings older destination inst start incoming sink type
  | _ :: rest, tag + 1 => structuralFlatVariantTransportPaths profile ready base bindings older destination inst start incoming sink rest tag
termination_by structural cases => cases
end

/-- Compare either public body for arbitrary list/map nesting with fixed
arrays, heterogeneous aggregates, active sum arms, and nominal, scalar, or string leaves. -/
def LinkedRecursiveCollectionBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming : Config (core3 grow) (HostState sig)) : Stored.TypeOf → Prop
  | .list element =>
    LinkedCollectionBody profile ready base bindings older site (.list element) element incoming (fun _ entries pointer bytes _ =>
      liveListTail profile ready base bindings site.destination site.inst element entries 0 route.output
        (liveCollectionField profile ready base bindings older site.destination site.inst element)
        site.reply site.referenceReply (fun _ => LinkedCallback.ChildFrameOver older) pointer bytes)
  | .map key element =>
    LinkedCollectionBody profile ready base bindings older site (.map key element) (.record (ABI.mapEntryFields key element)) incoming
      (fun _ entries pointer bytes _ => liveMapTailWith profile ready base bindings
        (liveCollectionMapEntry profile ready base bindings older site.destination site.inst key element route.output)
        site.destination site.inst key element entries 0 route.output
        (liveCollectionField profile ready base bindings older site.destination site.inst element)
        site.reply site.referenceReply (fun _ => LinkedCallback.ChildFrameOver older) pointer bytes)
  | _ => False

abbrev LinkedStringRecursiveMapBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedRecursiveCollectionBody profile ready base bindings older site incoming (.map .string element)

/-- Compare the descriptor and reached nominal value at the end of a
string-key replay. Late refusal leaves the value program unexecuted, even
when its first instruction is a flat-map width read. -/
def StringKeyNominalValue (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value : Stored.Endpoints.RecordLower.Field)
    (address issueIndex : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let afterKey := address + (layout destination.width key.field.type).size
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
  let pending := mapValueProgram destination inst mode value afterKey canonNext
  let place := alignTo afterKey (layout destination.width value.type).alignment
  let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkNext (verdict.mapError (.nested issueIndex))
  let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
    | .error issue => pure (.error issue)
    | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width value 1 (.memory place)) >>= report
  StringKeyReplay profile ready base bindings older origin destination inst key address left right check canon checked (fun _ => pending) →
  StringKeyThen profile ready base bindings older destination inst key address left right check canon checked (fun _ => pending)
    (fun _ lhs rhs cursor _ => CollectionSegment profile ready base bindings older lhs rhs cursor checkNext canonNext 0
      (· = pending) (fun reached => Core3.Grows origin.core reached.core))

/-- Cut the actual map traversal at its selected entry and preserve its exact
remainder. Both the successful continuation and the stopped suffix retain the
original traversal finish, which can publish the descriptor and reply. -/
def LinkedStringMapEntry (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Fin entries.length) (origin : CStore (core3 grow)) (basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (next : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop :=
        fun lhs _ _ _ => Core3.Grows origin.core lhs.store.core) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let destination := site.destination
  let cx := destination.context site.inst
  let type : Stored.TypeOf := .record (mapEntryFields .string element)
  let stride := (layout destination.width type).size
  let ptr := basePtr + index.val * stride
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) route.output
  let item := entries[index.val]
  let rest := entries.drop (index.val + 1)
  let checkTail := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
    | .error issue => pure (.error issue)
    | .ok () => OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width
        rest stride (ptr + stride) (index.val + 1)) >>= checkNext
  let canonTail := fun (_ : Unit) => CanonicalTree.elements Limits.spec Quirks.none cx destination.width
    rest mode stride (ptr + stride) >>= canonNext
  left.ctl = check.control (OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx
    destination.width (entries.drop index.val) stride ptr index.val >>= checkNext) →
  right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx destination.width
    (entries.drop index.val) mode stride ptr >>= canonNext) →
  ∃ (key : LinkedCallback.StringField) (value : Field), item = .aggregate type [key.field, value] ∧
    let keyArea := layout destination.width key.field.type
    let keyPtr := alignTo ptr keyArea.alignment
    let afterKey := keyPtr + keyArea.size
    let pending := mapValueProgram destination site.inst mode value afterKey canonTail
    let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
    let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkTail (verdict.mapError (.nested index.val))
    let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
          value 1 (.memory valuePtr)) >>= report
    StringKeyThen profile ready base bindings older destination site.inst key keyPtr left right check canon checked (fun _ => pending)
      (fun _ lhs rhs cursor _ => CollectionSegmentThen profile ready base bindings older lhs rhs cursor checkTail canonTail 0
        (· = pending) (fun _ reached peer nextCheck => next reached peer cursor nextCheck))

/-- Exact controls for a reached suffix, including the original finish. -/
def LinkedStringMapAt {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let stride := (layout site.destination.width (.record (mapEntryFields .string element))).size
  let address := basePtr + index * stride
  let cx := site.destination.context site.inst
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
  left.ctl = check.control (OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx
    site.destination.width (entries.drop index) stride address index >>= checkNext) ∧
  right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx site.destination.width
    (entries.drop index) mode stride address >>= canonNext)

/-- Compare a suffix of the actual map traversal. Only a returned key and
value enter the next suffix; a suspended allocator, refusal or trap does not.
Each link retains its visible trace and the trails of older occurrences. -/
def LinkedStringMapTraversal (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index : Nat) (origin : CStore (core3 grow)) (basePtr : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (finish : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop :=
        fun _ _ _ _ => True) : Prop :=
  LinkedStringMapAt site element entries index basePtr left right check canon checkNext canonNext ∧
    if present : index < entries.length then
      LinkedStringMapEntry profile ready base bindings older site element entries ⟨index, present⟩ origin basePtr
        left right check canon checkNext canonNext (fun lhs rhs cursor peer =>
          LinkedStringMapTraversal profile ready base bindings older site element entries (index + 1) origin basePtr
            lhs rhs cursor peer checkNext canonNext finish)
    else
      LinkedCallback.ChildFrameOver older left right check canon ∧
        left.ctl = check.control (checkNext (.ok ())) ∧ right.ctl = canon.control (canonNext ()) ∧
        Core3.Grows origin.core left.store.core ∧ finish left right check canon
termination_by entries.length - index

/-- The actual post-prepare map body for either public give. Only a complete
entry traversal executes the outer descriptor, which can itself trap. -/
def LinkedStringMapBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (basePtr : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (index : Nat := 0) (origin : CStore (core3 grow) := left.store) : Prop :=
  let publish : Session grow sig route.output.Result := Stored.Endpoints.ListLower.publish
    (site.destination.context site.inst) site.destination.width basePtr entries.length route.output
  let checkTail := PayloadPrefix.checkedSequenceNext (.nested 0) (fun (_ : Unit) => publish >>= fun value => pure (.ok value)) site.reply
  let canonTail := fun (_ : Unit) => publish >>= site.referenceReply
  LinkedStringMapTraversal profile ready base bindings older site element entries index origin basePtr left right check canon
    checkTail canonTail (fun lhs rhs cursor _ =>
      CollectionSegment profile ready base bindings older lhs rhs cursor site.reply site.referenceReply 0 (fun _ => False))

def mapValueSuffix (destination : RecordDestination) (inst : InstId)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (keyField value : Stored.Endpoints.RecordLower.Field) (rest : List Stored.Endpoints.RecordLower.Field) (stride address : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) : Session grow sig (Ret (core3 grow)) :=
  open Stored.Endpoints.RecordLower ABI in
  let keyArea := layout destination.width keyField.type
  let keyPtr := alignTo address keyArea.alignment
  let cx := destination.context inst
  mapFieldPlacement cx mode fun reached =>
    let valPtr := alignTo (keyPtr + keyArea.size) (layout reached value.type).alignment
    CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory valPtr) >>= fun _ =>
      CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest mode stride (address + stride) >>= finish

/-- A map value guard stops after its key has run. Flat maps still have the
reached value-width read ahead of them; memory maps use allocation-time placement. -/
def MapValueStop (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
    (entries : List Stored.Endpoints.RecordLower.Field) (stride ptr : Nat)
    (finish : Unit → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  ∃ leading rest keyField value,
    entries = leading ++ .aggregate (.record (ABI.mapEntryFields key element)) [keyField, value] :: rest ∧
    stop = mapValueSuffix destination inst mode keyField value rest stride (ptr + leading.length * stride) finish

/-- A reached map can stop before entries at fresh preparation, or
after the key of the value currently being visited. -/
def MapReturnStop (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (output : Stored.Lower.Output) (ptr : Nat)
    (finish : output.Result → Session grow sig (Ret (core3 grow))) (stop : Session grow sig (Ret (core3 grow))) : Prop :=
  open Stored.Endpoints.RecordLower ABI in
  let area := layout destination.width (.record (mapEntryFields key element))
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
  stop = (PayloadPrefix.canonicalCollectionTail destination inst entries area output ptr mode >>= finish) ∨
  MapValueStop destination inst key element mode entries area.size ptr
    (fun _ => Stored.Endpoints.ListLower.publish (destination.context inst) destination.width ptr entries.length output >>= finish) stop

/-- Complete the actual public replies from a reached allocator return.
Only a returned descriptor rejoins both machines. A typed refusal records
the checked completion and rejoins its caller, leaving canonical suspended
at the actually reached program. A canonical trap executes no reply. -/
def CollectionSegmentReplies (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (checked canonical : Config (core3 grow) (HostState sig))
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) (offset : Nat := 1)
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True) : Prop :=
  ∃ (outcome : PayloadPrefix.Outcome route.output.Result) (checkLabels canonLabels : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)),
    Steps profile ready (specDispatch ready base) checked checkLabels left ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonLabels right ∧
    left.store = right.store ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    match outcome with
    | .returned value => ∃ before canonBefore checkBody canonBody,
        checkLabels = checkBody ++ [.tau, .tau, .tau] ∧ canonLabels = canonBody ++ [.tau] ∧
        Steps profile ready (specDispatch ready base) checked checkBody before ∧
        Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonBody canonBefore ∧
        (∀ dispatch, Steps profile ready dispatch before [.tau, .tau, .tau] left) ∧
        (∀ dispatch, Steps profile ready dispatch canonBefore [.tau] right) ∧
        left.host = before.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1 ∧
        right.host = canonBefore.host ∧ HostFrame.Related.Paired older left right ∧ afterReturn left right ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base)
          checked (.active 0 (depth + 1 + offset)) checkLabels left (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
          canonical (.active 0 (depth + 1 + offset)) canonLabels right (.active 0 depth))
    | .refused issue => ∃ (before : Config (core3 grow) (HostState sig)) (checkBody : Trace grow sig)
        (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
        (stop : Session grow sig (Ret (core3 grow))), stopsAt stop ∧
        checkLabels = checkBody ++ [.tau, .tau, .tau] ∧
        Steps profile ready (specDispatch ready base) checked checkBody before ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
          canonical (.active 0 (depth + offset)) canonLabels right (.active 0 depth)) ∧
        left.host = before.host.record (route.reply site.destination site.start.host.nextTicket (.error issue)).1 ∧
        (∀ dispatch, Steps profile ready dispatch before [.tau, .tau, .tau] left) ∧ right.ctl = canon.control stop ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base)
          checked (.active 0 (depth + 1 + offset)) checkLabels left (.active 0 depth))
    | .trapped reason => left.ctl = [] ∧ right.ctl = [] ∧ ∃ leading, PayloadPrefix.visible canonLabels = leading ++ [.trap reason]

/-- The error program has already reached the public reply on checked.
Only that machine runs a completion; the canonical path ends at the exact
configuration supplied by the traversal. -/
def publicRefusalSink (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered : Config (core3 grow) (HostState sig)) : RefusalSink grow sig where
  admits next := ∀ issue, ∃ reported, next issue = site.reply (.error reported)
  nested _ closed index issue := closed (.nested index issue)
  exit next issue observed lhs rhs cursor :=
    ∃ reported, next issue = site.reply (.error reported) ∧
      ComparedSlots profile ready base bindings site.checked entered observed lhs rhs ∧ lhs.store = rhs.store ∧
      ∃ (segments : List (Seg (core3 grow) (HostState sig))) (checkBody canonBody : Trace grow sig),
        let reply := route.reply site.destination site.start.host.nextTicket (.error reported)
        let resumed :=
          { lhs with
            host := lhs.host.record reply.1
            ctl := ⟨cursor.thread, .core ((core3 grow).resume lhs.store.core site.core (.values reply.2)) site.resume,
              segments⟩ :: cursor.rest }
        PayloadPrefix.visible checkBody = observed ∧ PayloadPrefix.visible canonBody = observed ∧
        (∀ dispatch place, ReturnFrame.Occurrence.Trail profile ready dispatch lhs (some place) [.tau, .tau, .tau] resumed
          ((ReturnFrame.Occurrence.Edit.pop : ReturnFrame.Occurrence.Edit (core3 grow) (HostState sig)).follow place)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base)
          site.checked (.active 0 (depth + 1)) (checkBody ++ [.tau, .tau, .tau]) resumed (.active 0 depth)) ∧
        (∀ depth, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
          entered (.active 0 depth) canonBody rhs (.active 0 depth))

/-- From actual collection allocation and placement, visit the reached
descendants in order. The cumulative trail supports either original caller
rejoins after publication or a checked-only refusal reply at a reached
nested guard. A trap or finite suspension need not reach either reply. -/
def LinkedCollectionRejoinPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming : Config (core3 grow) (HostState sig)) : Stored.TypeOf → Prop
  | .list element =>
    LinkedCollectionBody profile ready base bindings older site (.list element) element incoming fun entered entries =>
      liveListTailPaths site.destination site.inst element entries 0 route.output
        (liveRecursivePaths profile ready base bindings older site.destination site.inst site.checked entered 0
          (publicRefusalSink profile ready base bindings site entered) element)
        site.reply site.referenceReply
        (fun _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0)
  | .map key element =>
    LinkedCollectionBody profile ready base bindings older site (.map key element) (.record (ABI.mapEntryFields key element)) incoming
      fun entered entries => liveMapTailPaths (liveMapEntryPaths profile ready base bindings older site.destination site.inst key element
        route.output site.checked entered 0 (liveRecursivePaths profile ready base bindings older site.destination site.inst site.checked entered 0
          (publicRefusalSink profile ready base bindings site entered) element))
        site.destination site.inst key element entries 0 route.output site.reply site.referenceReply
        (fun _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0)
  | _ => False

/-- The same reached string plan can return words or store a descriptor.
On a finite allocator prefix the occurrence remains available without a reply. -/
def LinkedStringRejoinPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ str leading entered peer,
    site.field = str.field ∧ PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    entered.host = incoming.host ∧
    StringValuePaths profile ready base bindings older site.destination site.inst str route.output
      site.checked entered site.checked entered site.cursor peer site.reply site.referenceReply
      (fun _ _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0)
      [] 0

/-- The successful body continuation of a memory give is already the
actual public reply; there is no separate root descriptor to publish. -/
def MemoryRootFinish (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) : LinkedCallback.MemorySequence.Finish grow sig :=
  fun left right check canon => LinkedCallback.ChildFrameOver older left right check canon ∧
    left.ctl = check.control (site.reply (.ok ())) ∧ right.ctl = canon.control (site.referenceReply ())

/-- Enter the actual canonical memory root and compare the same compiled
field traversal used for children. Success and typed refusal target the
original caller, while trap and allocator cuts stay at their reached sites. -/
def LinkedMemoryRejoinPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig))
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True) : Prop :=
  ∃ leading entered peer, PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    entered.host = incoming.host ∧
    liveRecursivePaths profile ready base bindings older site.destination site.inst site.checked entered 0
      (publicRefusalSink profile ready base bindings site entered) (sig.payload site.tag)
      site.field 0 (flatNat pointer) site.reply site.referenceReply
      (fun _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0 afterReturn)
      [] site.checked entered site.cursor peer

/-- The original flat public entry and cumulative traversal. Only successful
children contribute words; a typed refusal runs the checked reply alone. -/
def LinkedFlatAggregateRejoinPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {type : Stored.TypeOf}
    (site : PayloadRoot.Site grow sig (.flat type)) (incoming : Config (core3 grow) (HostState sig))
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True) : Prop :=
  ∃ leading entered peer, PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    entered.host = incoming.host ∧
    liveFlatPaths profile ready base bindings older site.destination site.inst site.checked entered 0
      (publicRefusalSink profile ready base bindings site entered) (sig.payload site.tag)
      site.field 0 site.reply site.referenceReply
      (fun _ _ _ _ _ _ => CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0 afterReturn)
      [] site.checked entered site.cursor peer

/-- The installed caller's mark is separate from older request origins. If
it is not at the reached reply slot, the relation records its actual
coordinate or loss instead of asserting a rejoin of the original caller. -/
def PublicOccurrenceExit (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered : Config (core3 grow) (HostState sig))
    (verdict : Except Stored.Endpoints.RecordLower.Issue route.output.Result) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkBody canonBody mark,
    CoupledOccurrencePaths profile ready base bindings site.checked entered checkBody canonBody left right ∧
    PayloadPrefix.visible checkBody = seen ∧ PayloadPrefix.visible canonBody = seen ∧ left.store = right.store ∧
    Trail profile ready (specDispatch ready base) site.checked (some (.active 0 0)) checkBody left mark ∧
    Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) entered (some (.active 0 0)) canonBody right mark ∧
    (mark = some (.active 0 0) →
      let reply := route.reply site.destination site.start.host.nextTicket verdict
      ∃ checked canonical,
        checked.host = left.host.record reply.1 ∧
        (∀ place, Trail profile ready (specDispatch ready base) left (some place) [.tau, .tau, .tau] checked
          ((Edit.pop : Edit (core3 grow) (HostState sig)).follow place)) ∧
        match verdict with
        | .error _ => canonical = right
        | .ok _ => canonical.host = right.host ∧ HostFrame.Related.Paired older checked canonical ∧
          ∀ place, Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) right (some place) [.tau] canonical
            ((Edit.pop : Edit (core3 grow) (HostState sig)).follow place))

/-- After a checked-only reply the corresponding older origins can be at
different positions. Both still follow their own reached machine path. -/
def RequestExitOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkLabels canonLabels, PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
    ∀ mark : Location, ∃ leftMark rightMark,
      Trail profile ready (specDispatch ready base) start (some mark) checkLabels checked leftMark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (some mark) canonLabels canonical rightMark

def RequestExitKind (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {α : Type}
    (verdict : Except Stored.Endpoints.RecordLower.Issue α) (stopped checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  match verdict with
  | .error _ => canonical = stopped
  | .ok _ => HostFrame.Related.Paired older checked canonical

def publicOccurrenceSink (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered : Config (core3 grow) (HostState sig)) : RefusalSink grow sig where
  admits next := ∀ issue, ∃ reported, next issue = site.reply (.error reported)
  nested _ closed index issue := closed (.nested index issue)
  exit next issue seen left right _ := ∃ reported, next issue = site.reply (.error reported) ∧
    PublicOccurrenceExit profile ready base bindings older site entered (.error reported) seen left right

/-- Keep the reached refused continuation and attach a local observation
of the typed error at the same checked/canonical cut. -/
def publicOccurrenceSinkWith (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered : Config (core3 grow) (HostState sig))
    (refused : Stored.Endpoints.RecordLower.Issue → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop) : RefusalSink grow sig :=
  { publicOccurrenceSink profile ready base bindings older site entered with
    exit := fun next issue seen left right _ => ∃ reported, next issue = site.reply (.error reported) ∧
      PublicOccurrenceExit profile ready base bindings older site entered (.error reported) seen left right ∧
      refused reported seen left right }

/-- The flat body resolves each reached compiled field and accumulates older
active and saved tracks all the way to the actual public reply. The canonical
entry retains its paths from the live original request. -/
def LinkedFlatOccurrenceBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {type : Stored.TypeOf}
    (site : PayloadRoot.Site grow sig (.flat type)) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ canonLabels entered peer, PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    structuralFlatOccurrencePaths profile ready base bindings older site.destination site.inst site.checked entered
      (publicOccurrenceSink profile ready base bindings older site entered) (sig.payload site.tag)
      site.field 0 site.reply site.referenceReply
      (fun words seen left right _ _ => PublicOccurrenceExit profile ready base bindings older site entered (.ok words) seen left right)
      [] site.checked entered site.cursor peer

/-- The memory body uses the same exit relation as flat lowering. Each
child visits the real memory program and contributes its reached paths. -/
def LinkedMemoryOccurrenceBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ canonLabels entered peer, PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    structuralMemoryOccurrencePaths profile ready base bindings older site.destination site.inst site.checked entered
      (publicOccurrenceSink profile ready base bindings older site entered) (sig.payload site.tag)
      site.field 0 (flatNat pointer) site.reply site.referenceReply
      (fun seen left right _ _ => PublicOccurrenceExit profile ready base bindings older site entered (.ok ()) seen left right)
      [] site.checked entered site.cursor peer

/-- At a successful body endpoint, carry every older occurrence from the
original request. Only the reached original caller at the top licenses
the checked completion and common Core return. -/
def PublicSuccessTransport (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming entered : Config (core3 grow) (HostState sig))
    (checkEntry canonEntry : Trace grow sig) (value : route.output.Result) (seen : Trace grow sig)
    (left right : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkBody canonBody mark,
    PayloadPrefix.visible checkBody = seen ∧ PayloadPrefix.visible canonBody = seen ∧
    OccurrenceTransport profile ready base bindings site.start incoming (checkEntry ++ checkBody) (canonEntry ++ canonBody)
      left right [mark] ∧
    Trail profile ready (specDispatch ready base) site.checked (some (.active 0 0)) checkBody left mark ∧
    Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) entered (some (.active 0 0)) canonBody right mark ∧
    (mark = some (.active 0 0) → ∃ checked canonical,
      checked.host = left.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1 ∧
      canonical.host = right.host ∧ HostFrame.Related.Paired older checked canonical ∧
      OccurrenceTransport profile ready base bindings site.start incoming
        ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) ((canonEntry ++ canonBody) ++ [.tau]) checked canonical)

/-- The terminal observation is inside the recursive visitor, so it is
applied only at a reached success, not at a trap, refusal or suspension. -/
def LinkedMemoryTransportBodyWith (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig))
    (success : Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (refused : Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) →
      Stored.Endpoints.RecordLower.Issue → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop) : Prop :=
  ∃ canonLabels entered peer, PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    ∀ checkLabels, site.EntryPrefix profile ready base checkLabels site.checked →
      recursiveAllocatingTransportPaths profile ready base bindings older site.destination site.inst site.checked entered
        (publicOccurrenceSinkWith profile ready base bindings older site entered (refused checkLabels canonLabels entered)) (sig.payload site.tag)
        site.field 0 (flatNat pointer) site.reply site.referenceReply
        (fun seen left right _ _ => success checkLabels canonLabels entered seen left right)
        [] site.checked entered site.cursor peer

/-- The checked entry prefix is supplied by the placed branch of the cut.
The recursive visitor derives the terminal observation from reached paths. -/
def LinkedMemoryTransportBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedMemoryTransportBodyWith profile ready base bindings older site incoming
    (fun checkEntry canonEntry entered seen left right =>
      PublicSuccessTransport profile ready base bindings older site incoming entered checkEntry canonEntry () seen left right)
    (fun _ _ _ _ _ _ _ => True)

/-- The reached flat visitor keeps emitted words and occurrence transport
through the real fold, rather than a separately supplied body trail. -/
def LinkedFlatTransportBodyWith (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {type : Stored.TypeOf}
    (site : PayloadRoot.Site grow sig (.flat type)) (incoming : Config (core3 grow) (HostState sig))
    (success : Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) → List FlatValue → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (refused : Trace grow sig → Trace grow sig → Config (core3 grow) (HostState sig) →
      Stored.Endpoints.RecordLower.Issue → Trace grow sig →
      Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop) : Prop :=
  ∃ canonLabels entered peer, PayloadPrefix.visible canonLabels = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonLabels entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
    ∀ checkLabels, site.EntryPrefix profile ready base checkLabels site.checked →
      structuralFlatTransportPaths profile ready base bindings older site.destination site.inst site.checked entered
        (publicOccurrenceSinkWith profile ready base bindings older site entered (refused checkLabels canonLabels entered)) (sig.payload site.tag)
        site.field 0 site.reply site.referenceReply
        (fun words seen left right _ _ => success checkLabels canonLabels entered words seen left right)
        [] site.checked entered site.cursor peer

/-- The actual range verdict after an allocator return. A late reservation
refusal runs only the checked completion; canonical is at child entry with
the reached store, before any element write or descriptor publication. -/
def CollectionReturnFailure (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (pointer : Nat)
    (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout site.destination.width element
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width type route.output
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  let trap := fun reason => ∃ leftCount rightCount,
    Steps profile ready checkedDispatch checked (List.replicate leftCount .tau ++ [.trap reason]) (StepDefs.trapCfg checked) ∧
    Steps profile ready canonDispatch canonical (List.replicate rightCount .tau ++ [.trap reason]) (StepDefs.trapCfg canonical)
  checked.store = canonical.store ∧ ∃ bytes,
    (core3 grow).memSize? checked.store.core site.destination.memory = some bytes ∧
    if pointer ≠ alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + entries.length * area.size ≤ bytes then
      ∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
        let child := canonicalCollectionTail site.destination site.inst entries area route.output pointer mode >>= site.referenceReply
        let reply := route.reply site.destination site.start.host.nextTicket (.error (LinkedCallback.CollectionVisit.afterAllocation 0 issue))
        ∃ (canon : Cursor (E := core3 grow) (HostState sig)) (lhs rhs : Trace grow sig)
          (segments : List (Seg (core3 grow) (HostState sig))),
          visible lhs = [] ∧ visible rhs = [] ∧
          Steps profile ready checkedDispatch checked (lhs ++ [.tau, .tau, .tau])
            { checked with
              host := checked.host.record reply.1
              ctl := ⟨check.thread, .core ((core3 grow).resume checked.store.core site.core (.values reply.2)) site.resume,
                segments⟩ :: check.rest } ∧
          ReturnFrame.Occurrence.RetainsBelowTop profile ready canonDispatch canonical rhs
            { canonical with ctl := canon.control child }
    else trap .outOfBounds

/-- Classify each finite supported root callback prefix. Only an actual
return of the installed allocator occurrence can enter the failure cut. -/
def LinkedCollectionReturnFailures (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming : Config (core3 grow) (HostState sig))
    (type element : Stored.TypeOf) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  ∃ (entries : List Field) (leading : Trace grow sig) (entered : Config (core3 grow) (HostState sig))
    (peer : Cursor (E := core3 grow) (HostState sig)),
    site.field = .dynamic type element entries ∧ visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    let area := layout site.destination.width element
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width type route.output
    let lhs := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let rhs := canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply mode
    let checkedEntry := collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor lhs
    let canonEntry := collectionEntry site.destination site.inst area entries.length
      (specDispatch ready (LiveDispatch.host bindings base)) entered peer rhs
    ∀ {seen checked}, ClosedCallbackPrefix bindings profile ready base
        (fun resume => (∃ other, older resume other) ∨ resume = lhs) checkedEntry seen checked →
      ∃ checkLabels canonLabels canonical mark,
        AllocatorMark profile ready base bindings older checkedEntry canonEntry checkLabels canonLabels checked canonical mark ∧
        ComparedPaths profile ready base bindings site.checked entered seen checked canonical ∧
        ∀ pointer cursor, mark = some (.active 0 0) →
          checked.ctl = { cursor with frames := .prog lhs :: cursor.frames }.control (.pure (.nat pointer)) →
          CollectionReturnFailure profile ready base bindings site type element entries pointer checked canonical cursor

/-- A marked string-key map return either traps or refuses before any entry,
or reaches the recursive body with the original checked caller still tracked. -/
def LinkedStringMapReturn (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let checkedDispatch := specDispatch ready base
  let canonDispatch := specDispatch ready (LiveDispatch.host bindings base)
  CollectionSegmentReplies profile ready base bindings older site checked canonical
    (MapReturnStop site.destination site.inst .string element entries route.output pointer site.referenceReply) ∨
  ∃ (left right : Config (core3 grow) (HostState sig)) (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (checkLabels canonLabels callerLabels : Trace grow sig),
    RetainsBelowTop profile ready checkedDispatch checked checkLabels left ∧
    RetainsBelowTop profile ready canonDispatch canonical canonLabels right ∧
    PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
    Prefix profile ready checkedDispatch site.checked (.active 0 0) callerLabels left (.active 0 0) ∧
    LinkedStringMapBody profile ready base bindings older site element entries pointer left right check canon

/-- A traversal rooted at the prepared public body. Every reached allocator
prefix has a cumulative comparison. A completed entry advances to the actual
next suffix; a terminal segment carries the original caller result. -/
def LinkedStringMapPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (index basePtr : Nat) (leftStart rightStart left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig) (offset : Nat := 0) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix ReturnFrame.Occurrence in
  let destination := site.destination
  let cx := destination.context site.inst
  let type : Stored.TypeOf := .record (mapEntryFields .string element)
  let stride := (layout destination.width type).size
  let publish : Session grow sig route.output.Result := Stored.Endpoints.ListLower.publish cx destination.width basePtr entries.length route.output
  let checkNext := checkedSequenceNext (.nested 0) (fun (_ : Unit) => publish >>= fun value => pure (.ok value)) site.reply
  let canonNext := fun (_ : Unit) => publish >>= site.referenceReply
  let terminal := CollectionSegmentReplies profile ready base bindings older site leftStart rightStart
    (MapReturnStop destination site.inst .string element entries route.output basePtr site.referenceReply) offset
  if present : index < entries.length then
    let ptr := basePtr + index * stride
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) route.output
    let rest := entries.drop (index + 1)
    let checkTail := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => OwnedMemory.Claims.Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width
          rest stride (ptr + stride) (index + 1)) >>= checkNext
    let canonTail := fun (_ : Unit) => CanonicalTree.elements Limits.spec Quirks.none cx destination.width
      rest mode stride (ptr + stride) >>= canonNext
    ∃ (key : LinkedCallback.StringField) (value : Field), entries[index] = .aggregate type [key.field, value] ∧
      let keyArea := layout destination.width key.field.type
      let keyPtr := alignTo ptr keyArea.alignment
      let afterKey := keyPtr + keyArea.size
      let pending := mapValueProgram destination site.inst mode value afterKey canonTail
      let valuePtr := alignTo afterKey (layout destination.width value.type).alignment
      let report := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => checkTail (verdict.mapError (.nested index))
      let checked := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
            value 1 (.memory valuePtr)) >>= report
      let plan := storePlanFor Quirks.none destination.encoding destination.width key.value
      let checkString := fun addr => stringPlanTail cx destination.width (.memory keyPtr) plan addr >>= fun result => checked (.ok result)
      let canonString := fun addr => stringPlanTail cx destination.width (.memory keyPtr) plan addr >>= fun _ => pending
      let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checkString) }
      let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonString) }
      ComparedSlots profile ready base bindings left right [] checkBody canonBody ∧
      LiveStringPaths profile ready base bindings older cx checkString canonString leftStart rightStart
        (fun _ lhs rhs cursor _ observations => terminal ∨
          ∃ nextLeft nextRight nextCanon suffix,
            ComparedSlots profile ready base bindings lhs rhs suffix nextLeft nextRight ∧
            LinkedStringMapPaths profile ready base bindings older site element entries (index + 1) basePtr
              leftStart rightStart nextLeft nextRight cursor nextCanon (observations ++ suffix) offset)
        plan.steps.length checkBody canonBody check canon seen offset
  else terminal
termination_by entries.length - index

/-- The actual paths after a marked outer allocator return, for either public give.
Before entry, refusal retains the outer frame offset. After entry, each finite
allocator prefix is tracked from the return state and terminal replies use the
original caller. -/
def LinkedStringMapReturnPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop :=
  CollectionSegmentReplies profile ready base bindings older site checked canonical
    (MapReturnStop site.destination site.inst .string element entries route.output pointer site.referenceReply) ∨
  ∃ left right canon seen, ComparedSlots profile ready base bindings checked canonical seen left right 1 ∧
    LinkedStringMapPaths profile ready base bindings older site element entries 0 pointer checked canonical left right
      check canon seen 1

/-- From the real linked call on the canonical side, compare every classified
outer allocator prefix after checked admission. A natural-pointer return
of the installed occurrence feeds the original replies proof. -/
def LinkedStringMapDispatch (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout site.destination.width (.record (mapEntryFields .string element))
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
  let first := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
  let second := canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply mode
  let leftEntry := collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first
  let canonical := specDispatch ready (LiveDispatch.host bindings base)
  ∃ leading entered peer, visible leading = [] ∧ Steps profile ready canonical incoming leading entered ∧
    entered.host = incoming.host ∧
    let rightEntry := collectionEntry site.destination site.inst area entries.length canonical entered peer second
    ∀ {seen checked}, ClosedCallbackPrefix bindings profile ready base
        (fun resume => (∃ paired, older resume paired) ∨ resume = first) leftEntry seen checked →
      ∃ checkLabels canonLabels reached mark,
        AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels checked reached mark ∧
        HostFrame.Related.Paired (ReturnFrame.Extend older first second) checked reached ∧
        ComparedPaths profile ready base bindings site.checked incoming seen checked reached ∧
        ∀ pointer check, mark = some (.active 0 0) →
          checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
          LinkedStringMapReturnPaths profile ready base bindings older site element entries pointer checked reached check

abbrev CollectionReplies (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (checked canonical : Config (core3 grow) (HostState sig))
    (childEntry : Session grow sig (Ret (core3 grow))) : Prop :=
  CollectionSegmentReplies profile ready base bindings older site checked canonical (· = childEntry)

/-- Stops before the recursive body. A checked preflight refusal resumes its
caller; a bad placement traps the checked machine. Neither executes the
canonical body, whose memory placement is a precondition. -/
inductive RootStop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) :
    Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | refused (issue : Stored.Endpoints.RecordLower.Issue) {labels}
      (silent : PayloadPrefix.visible labels = [])
      (edge : Transition profile ready base site.start (.give route (.refused issue)) labels (site.refusedReply issue)) :
      RootStop profile ready base site labels (site.refusedReply issue)
  | placementTrap (reason : TrapReason) (count : Nat)
      (edge : Transition profile ready base site.start (.give route (.placementTrap reason))
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg site.checked)) :
      RootStop profile ready base site (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg site.checked)

/-- A finite decomposition of a checked run into scheduler segments and
compared gives. The canonical body of a give is itself a plan, so callouts
under a parked allocator can be compared before following the outer suffix.
Local body evidence names the actual replies or stop; it does not supply a
run at the replacement host or the older paired frames. -/
inductive NestedPlan (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → Trace grow sig → Config (core3 grow) (HostState sig) → Prop where
  | segment {start labels finish}
      (run : Steps profile ready (specDispatch ready base) start labels finish) :
      NestedPlan bindings profile ready base start labels finish
  | localSegment {start labels finish}
      (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish) :
      NestedPlan bindings profile ready base start labels finish
  | closedGive {start count} (callout : LinkedCallback.ClosedGive bindings start)
      (run : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) callout.resume) :
      NestedPlan bindings profile ready base start (List.replicate count .tau) callout.resume
  | syncReady {start task inst thread frames rest}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
        syncLiftCandidates task (start.store.instCandidates (ready current) inst))), frames⟩ :: rest)
      (agrees : LinkedCallback.ReadyAgreement ready start inst) :
      NestedPlan bindings profile ready base start [.tau] { start with ctl := ⟨thread,
        .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) inst)), frames⟩ :: rest }
  | commit {start target index} (resolve : ComponentCall.Delivery.LinkedResolution start target index) :
      NestedPlan bindings profile ready base start (List.replicate 17 .tau) resolve.committed
  | poll {start target index result suffix} (poll : ComponentCall.Delivery.ParkedPoll start target profile)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (branch : BufferBranch start.store poll.memory (flatNat poll.out) result suffix) :
      NestedPlan bindings profile ready base start (pollLabels poll ++ suffix)
        (result.finish (pollReply poll index) { start with store := StepDefs.lockdownSt poll.delivered, ctl := [] })
  | waitBlock {start} (wait : ComponentCall.Delivery.ParkedWait start) (empty : start.store.wsetHasEvent wait.ws = false) :
      NestedPlan bindings profile ready base start (List.replicate 13 .tau) wait.blocked
  | waitReady {start} (wait : ComponentCall.Delivery.ParkedWait start) (available : start.store.wsetHasEvent wait.ws = true)
      (early : Bool) (allowed : Allowed profile (.earlyReturn .waitableSetWait) early) :
      NestedPlan bindings profile ready base start (ComponentCall.Delivery.ParkedWait.readyLabels early)
        (if early then wait.early else wait.blocked)
  | waitResume {initial start} {wait : ComponentCall.Delivery.ParkedWait initial}
      (resume : ComponentCall.Delivery.WaitResume wait start) (saved : start.cont? wait.thread = some wait.saved) :
      NestedPlan bindings profile ready base start (List.replicate 4 .tau) resume.reached
  | waitTake {initial start target index result suffix} {wait : ComponentCall.Delivery.ParkedWait initial}
      (delivery : ComponentCall.Delivery.WaitDelivery wait start profile target)
      (focused : start.ctl = ⟨some wait.thread, .prog wait.takeEvent, .core wait.core wait.next :: wait.segments⟩ :: start.ctl.drop 1)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (branch : BufferBranch delivery.delivered wait.memory (flatNat wait.out) result suffix) :
      NestedPlan bindings profile ready base start (delivery.labels ++ suffix)
        (result.finish (delivery.resumed index) { start with store := StepDefs.lockdownSt delivery.delivered, ctl := [] })
  | cancelReturned {start target index} (cancel : ComponentCall.Delivery.ParkedCancel start target)
      (pending : ComponentCall.Delivery.PendingAt start.store target index)
      (available : ComponentCall.Delivery.CancelAvailable start.store target) :
      NestedPlan bindings profile ready base start (List.replicate 15 .tau) cancel.resumed
  | cancelRequest {start target} (cancel : ComponentCall.Delivery.ParkedCancel start target) (record : Subtask)
      (live : start.store.subtask? target = some record) (unresolved : record.state.resolved = false)
      (notDelivered : record.lenders.isSome = true) (notRequested : record.cancellationRequested = false)
      (notJoined : record.common.wset = none) :
      NestedPlan bindings profile ready base start (List.replicate 14 .tau) (cancel.callbackEntry record ready base)
  | cancelReentry {start target callee} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.TaskCancelAdmission cancel) (mode : ComponentCall.Delivery.TaskCancelReentry request ready)
      (saved : start.cont? request.implicitThread = some callee) :
      NestedPlan bindings profile ready base start (List.replicate request.reentrySteps .tau) (request.reentered callee)
  | cancelCallbackDone {start target} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.StartedCancel cancel) :
      NestedPlan bindings profile ready base start (List.replicate 20 .tau) request.callbackReturned
  | cancelPark {initial start target} {cancel : ComponentCall.Delivery.ParkedCancel initial target}
      (wait : ComponentCall.Delivery.SyncCancelWait cancel start) :
      NestedPlan bindings profile ready base start (List.replicate 5 .tau) wait.blocked
  | cancelResume {initial start target} {cancel : ComponentCall.Delivery.ParkedCancel initial target}
      (resume : ComponentCall.Delivery.SyncCancelResume cancel start) (saved : start.cont? cancel.thread = some cancel.saved) :
      NestedPlan bindings profile ready base start (List.replicate 3 .tau) resume.reached
  | cancelFinish {initial start target rest} (cancel : ComponentCall.Delivery.ParkedCancel initial target) (record : Subtask)
      (focused : start.ctl = ⟨some cancel.thread, .prog (ComponentCall.Delivery.ParkedCancel.finish target),
        .core cancel.core cancel.next :: cancel.segments⟩ :: rest)
      (live : start.store.subtask? target = some record) (resolved : record.state.resolved = true)
      (pending : record.common.pending = some (.subtask target)) :
      NestedPlan bindings profile ready base start (List.replicate 6 .tau) (cancel.finishReply start record.state rest)
  | sequence {start middle finish leading trailing}
      (front : NestedPlan bindings profile ready base start leading middle)
      (back : NestedPlan bindings profile ready base middle trailing finish) :
      NestedPlan bindings profile ready base start (leading ++ trailing) finish
  | rootStop {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings) {labels checked}
      (stop : RootStop profile ready base site labels checked) :
      NestedPlan bindings profile ready base site.start labels checked
  | compilerStop {start route issue count} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (refused : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) (selection.compilerRefused issue)) :
      NestedPlan bindings profile ready base start (List.replicate count .tau) (selection.compilerRefused issue)
  | give {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {entryLabels checkLabels referenceLabels reached reference checked baseline}
      (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
      (body : NestedPlan bindings profile ready base (site.reference site.referenceReply) (referenceLabels ++ [.tau]) baseline)
      (value : route.output.Result)
      (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels) :
      NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked
  | stop {route} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      {entryLabels checkLabels referenceLabels reached reference phase check}
      (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
      (body : NestedPlan bindings profile ready base (site.reference site.referenceReply) referenceLabels reference)
      (stop : GiveStop site check phase referenceLabels reached reference)
      (store : reached.store = reference.store)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels) :
      NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels) reached

/-- An exact callback trace reaches a dispatch lookup not covered by the
classified window. The prefix retains its specialized edges, and the
source suffix is retained but not replayed. A window ending at a lifted
install does not assert that the subsequent arena read will disagree. -/
def CallbackOverlayCut (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (start : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ middle after leading window suffix, labels = leading ++ window ++ suffix ∧
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start leading middle ∧
    Dispatch.LookupCut profile ready bindings callees middle window after ∧
    Steps profile ready (Dispatch.coreOnly ready bindings) after suffix finish

/-- At a fully classified window, retain both the exact dispatcher comparison
and the specialized edges needed to replay against a paired host. -/
def CallbackOverlayPlan (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (start : Config (core3 grow) (HostState sig))
    (labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  Dispatch.Compatible profile ready bindings callees start labels finish ∧
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start labels finish

/-- The comparison at an actual successful return. If a dispatcher window
cannot be transported, the checked/canonical replies from the narrower
comparison remain evidence, not a claim of a live canonical reply. -/
def LinkedGiveExit (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (entryLabels : Trace grow sig) (value : route.output.Result)
    (reached reference : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checkLabels canonLabels checked baseline,
    LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline ∧
    (NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
        (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∨
      CallbackOverlayCut bindings profile ready callees site.checked checkLabels reached ∨
      CallbackOverlayCut bindings profile ready callees (site.reference site.referenceReply) canonLabels reference)

/-- Reasons to stop at an actual live configuration. A local checked stop
has a matched store and observed trace, but does not rejoin (including when
the plan has a later checked-only suffix). Unselected roots are not assumed
to retain their previous tree across earlier compared episodes. -/
inductive NestedCut (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) → Prop where
  | request {before incoming label after}
      (paired : HostFrame.Related.Paired older before incoming)
      (install : GiveInstall bindings (specDispatch ready base) before label after) :
      NestedCut bindings profile ready base older incoming
  | boundary {before incoming label after reached}
      (paired : HostFrame.Related.Paired older before incoming)
      (cut : HostFrame.Related.Boundary older before incoming label after reached)
      (checkedStep : Step profile ready (specDispatch ready base) before label after)
      (referenceStep : Step profile ready (specDispatch ready (host bindings base)) incoming label reached) :
      NestedCut bindings profile ready base older reached
  | unselected {route incoming} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (paired : HostFrame.Related.Paired older site.start incoming)
      (selection : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle ≠ some site.tree) :
      NestedCut bindings profile ready base older incoming
  | rootStop {route reached labels checked} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
      (stop : RootStop profile ready base site labels checked)
      (installed : HostFrame.Related.Paired older (site.reference site.referenceReply) reached) :
      NestedCut bindings profile ready base older reached
  | compilerLookup {start route incoming} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (paired : HostFrame.Related.Paired older start incoming)
      (different : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle ≠ some selection.tree) :
      NestedCut bindings profile ready base older incoming
  | compilerStop {start route issue reached count} {request : CoreGiveRequest bindings start}
      (selection : request.Selected route) (refused : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready base) start (List.replicate count .tau) (selection.compilerRefused issue))
      (installed : HostFrame.Related.Paired older selection.canonicalPending reached) :
      NestedCut bindings profile ready base older reached
  | publication {start target index incoming} (resolve : ComponentCall.Delivery.LinkedResolution start target index)
      (paired : HostFrame.Related.Paired older start incoming)
      (different : ¬ ∃ writer, incoming.host.writer.register resolve.tree = .ok writer ∧
        writer.accepted.length = resolve.writer.accepted.length) :
      NestedCut bindings profile ready base older incoming
  | cancelReadiness {start target incoming} {cancel : ComponentCall.Delivery.ParkedCancel start target}
      (request : ComponentCall.Delivery.TaskCancelAdmission cancel) (mode : ComponentCall.Delivery.TaskCancelReentry request ready)
      (paired : HostFrame.Related.Paired older start incoming)
      (different : ¬ (request.callee.state = .started →
        request.markedStore.threadReady (ready incoming.host) request.implicitThread = true)) :
      NestedCut bindings profile ready base older incoming
  | stopped {route phase checkLabels referenceLabels liveLabels liveStart checked reference reached check}
      (site : PayloadRoot.Site grow sig route) (stop : GiveStop site check phase referenceLabels checked reference)
      (checkedBody : Steps profile ready (specDispatch ready base) site.checked checkLabels checked)
      (referenceBody : Steps profile ready (specDispatch ready (host bindings base)) liveStart liveLabels reached)
      (paired : HostFrame.Related.Paired older reference reached)
      (store : checked.store = reached.store)
      (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible liveLabels) :
      NestedCut bindings profile ready base older reached

/-- Use the actual public entry cut before asking for a recursive body comparison. -/
inductive RootAdmission (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (body : Prop) : Prop where
  | stopped {labels checked} (stop : RootStop profile ready base site labels checked)
      (plan : NestedPlan bindings profile ready base site.start labels checked) :
      RootAdmission bindings profile ready base site body
  | entered {labels} (entry : Transition profile ready base site.start (.give route .entered) labels site.checked)
      (compared : body) : RootAdmission bindings profile ready base site body

/-- Entry and the recursive success continuation for either public ABI under
the worker's linked dispatcher. This supplies no callback return or progress. -/
def LinkedRootExit (bindings : List (Binding sig)) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) (route : GiveEffectRoute) : PayloadRoot.Site grow sig route → Prop :=
  match route with
  | .memory _ => fun site => ∃ depth,
    RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedMemoryBody site depth profile ready bindings (fun reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels () reached reference))
  | .flat _ => fun site => ∃ flatDepth entryDepth,
    RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedFlatResult site flatDepth entryDepth profile ready bindings (fun value reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels value reached reference))

/-- Compiler rejection has no emitter or canonical typed error. Success
supplies the real compiled site, whose later entry guards still execute. -/
inductive ReachedGiveAdmission (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)} {start : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings start} {route : GiveEffectRoute} (selection : request.Selected route) : Prop where
  | refused {issue count} (preflight : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (List.replicate count .tau) (selection.compilerRefused issue))
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (exit : LinkedRootExit bindings profile ready callees route (selection.site tag payload arity children field))

/-- At the real returned callers, replay a finite checked suffix under the
fixed dispatcher. Stop at reached nested installs, unequal reads, or
substituted returns. Without older substitutions, closed delivery can
continue from the actual scheduler records and the reached live journal. -/
structure RejoinedWorkerTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop where
  replay : ∀ {labels finish}, Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
    checked labels finish →
    PairedReplay bindings profile ready (ComponentCall.hostWithComponent bindings callees) older checked canonical labels finish
  delivery : (∀ first second, ¬ older first second) → ∀ {actions labels finish outgoing},
    JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      checked canonical.host actions labels finish outgoing →
    Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) checked labels finish ∧
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
      canonical labels (HostFrame.replace finish outgoing) ∧
    (canonical.host.writer.accepted = checked.host.writer.accepted → outgoing.writer.accepted = finish.host.writer.accepted)

/-- The all-location body for the route chosen by the reached live selector. -/
def RecursiveGiveOccurrencePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) : (route : GiveEffectRoute) → PayloadRoot.Site grow sig route → Prop
  | .memory _, site => LinkedMemoryOccurrenceBody profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
  | .flat _, site => LinkedFlatOccurrenceBody profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming

/-- The recursive body and caller paths for whichever ABI the live selector
chose. A reached reply carries its next worker comparison, but neither a
reply nor an allocator return is required. -/
def RecursiveGivePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) : (route : GiveEffectRoute) → PayloadRoot.Site grow sig route → Prop
  | .memory _, site => LinkedMemoryRejoinPaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
    (RejoinedWorkerTail profile ready bindings callees older)
  | .flat _, site => LinkedFlatAggregateRejoinPaths profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
    (RejoinedWorkerTail profile ready bindings callees older)

/-- The canonical root has installed its real body but has not executed it.
Record the original occurrence trail at this cut; the checked side can
already have issued a refusal or entered lockdown. -/
def PendingRecursiveRoot (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (incoming : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ leading entered, PayloadPrefix.visible leading = [] ∧
    (∀ place, ReturnFrame.Occurrence.Prefix profile ready
      (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
      incoming place leading entered
      (((ReturnFrame.Occurrence.Edit.push (.core site.core site.resume)).follow place).getD place)) ∧
    HostFrame.Related.Paired older (site.reference site.referenceReply) entered ∧ entered.host = incoming.host

/-- The checked side records the typed reply and pops its Core caller. The
canonical side stays at the exact already reached child entry, so its older
occurrences keep their pre-reply positions. -/
def PublicCollectionRefusalOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (incoming checked canonical : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (type element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field) (pointer : Nat) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix ReturnFrame.Occurrence in
  let area := layout site.destination.width element
  let mode := CanonicalTree.EntryMode.forOutput site.destination.width type route.output
  ∀ bytes, (core3 grow).memSize? checked.store.core site.destination.memory = some bytes →
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    ∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
      let reply := route.reply site.destination site.start.host.nextTicket (.error (LinkedCallback.CollectionVisit.afterAllocation 0 issue))
      let child := canonicalCollectionTail site.destination site.inst entries area route.output pointer mode >>= site.referenceReply
      ∃ (canon : Cursor (E := core3 grow) (HostState sig)) (segments : List (Seg (core3 grow) (HostState sig)))
          (checkLabels canonLabels : Trace grow sig),
        let resumed := (core3 grow).resume checked.store.core site.core (.values reply.2)
        let left := { checked with host := checked.host.record reply.1, ctl := ⟨cursor.thread, .core resumed site.resume, segments⟩ :: cursor.rest }
        let right := { canonical with ctl := canon.control child }
        visible checkLabels = seen ∧ visible canonLabels = seen ∧ left.store = right.store ∧
        ∀ mark : Option Location, ∃ atReply,
          Trail profile ready (specDispatch ready base) site.start mark checkLabels left
            (atReply.bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow) ∧
          Trail profile ready (specDispatch ready (host bindings base)) incoming mark canonLabels right atReply

/-- From the original public request to the actual installed collection
allocator, then to the first range/recheck outcome if that occurrence returns.
The initial checked and reference programs are the real public entries. -/
def PublicCollectionOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (incoming : Config (core3 grow) (HostState sig)) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  let area := ABI.layout site.destination.width element
  let mode := Stored.Endpoints.RecordLower.CanonicalTree.EntryMode.forOutput site.destination.width type route.output
  let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
  let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply mode
  ∃ entered, ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
    ComparedOccurrencePaths profile ready base bindings site.start incoming [] site.checked entered ∧
    ∀ {seen finish}, ClosedCallbackPrefix bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first) seen finish →
      ∃ checkLabels canonLabels reached mark,
        AllocatorMark profile ready base bindings older
          (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
          (PayloadPrefix.collectionEntry site.destination site.inst area entries.length
            (specDispatch ready (host bindings base)) entered canon second) checkLabels canonLabels finish reached mark ∧
        ComparedOccurrencePaths profile ready base bindings site.start incoming seen finish reached ∧
        (∀ pointer (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
          mark = some (.active 0 0) →
          finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
          CollectionRangeOccurrences profile ready base bindings older site.start incoming finish reached seen
            cursor site.destination area entries.length pointer (Stored.Endpoints.RecordLower.Field.listObjects entries)
            (fun addr verdict => PayloadPrefix.checkedCollectionTail site.destination site.inst entries area 0 route.output addr verdict >>= site.reply)
            (fun addr => PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output addr mode >>= site.referenceReply) ∧
          PublicCollectionRefusalOccurrences profile ready base bindings site incoming finish reached seen cursor type element entries pointer)

/-- Classify the reached guard before recursive traversal starts. A
checked placement trap has its actual lockdown; it is not evidence that
the unexecuted canonical program has trapped at the same point. -/
inductive ReachedRecursiveRoot (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig))
    {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) : Prop where
  | refused {issue labels} (silent : PayloadPrefix.visible labels = [])
      (checked : ∀ place, ReturnFrame.Occurrence.Trail profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start (some place) (labels ++ [.tau, .tau, .tau]) (site.refusedReply issue) (some place))
      (pending : PendingRecursiveRoot profile ready bindings callees older site incoming)
  | placementTrap {reason count}
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .error reason)
      (checked : site.EntryTrap profile ready (ComponentCall.hostWithComponent bindings callees)
        (List.replicate count .tau ++ [.trap reason]))
      (pending : PendingRecursiveRoot profile ready bindings callees older site incoming)
  | placed {labels} (silent : PayloadPrefix.visible labels = [])
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
      (prepared : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
      (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) labels site.checked)
      (pending : PendingRecursiveRoot profile ready bindings callees older site incoming)
      (body : RecursiveGivePaths profile ready bindings callees older incoming route site)

/-- Compare a give at its actual Core installation. A compiler refusal
can rejoin only the checked caller; the canonical body has not executed.
Successful compilation supplies the real checked entry and the recursive
paths from the live canonical caller, not from a fresh reference host. -/
inductive ReachedRecursiveGive (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings start}
    {route : GiveEffectRoute} (selection : request.Selected route)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) : Prop where
  | refused {issue count leading entered} (preflight : selection.preflight = .error issue)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (List.replicate count .tau) (selection.compilerRefused issue))
      (silent : PayloadPrefix.visible leading = [])
      (canonical : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming leading entered)
      (pending : HostFrame.Related.Paired older selection.canonicalPending entered)
      (unchangedHost : entered.host = incoming.host)
      (occurrences : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees)
        bindings start incoming [] (selection.compilerRefused issue) entered)
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (cut : ReachedRecursiveRoot profile ready bindings callees older incoming (selection.site tag payload arity children field))
      (occurrences : PayloadRoot.Cut (selection.site tag payload arity children field) profile ready bindings
        (RecursiveGiveOccurrencePaths profile ready bindings callees older incoming route (selection.site tag payload arity children field))
        (ComponentCall.hostWithComponent bindings callees))

/-- The comparison domain for a successfully compiled root. A compiler
refusal does not need the recursive body theorem at all. -/
def RecursiveGiveDomain {bindings : List (Binding sig)} {start : Config (core3 grow) (HostState sig)}
    {request : CoreGiveRequest bindings start} {route : GiveEffectRoute} (selection : request.Selected route) : Prop :=
  ∀ tag payload arity children field plan, selection.tree = .tag ⟨tag, payload⟩ arity children →
    selection.preflight = .ok (field, plan) → RecursiveCollectionType (sig.payload tag)

/-- Classify a reached Core give without choosing its route or body in
advance. The open lookup names the exact demanded handle. An ABI refusal
actually rejoins both callers, unlike a later checked compiler refusal. -/
inductive RecursiveRequestCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} (request : CoreGiveRequest bindings start)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (incoming : Config (core3 grow) (HostState sig)) : Prop where
  | lookup {handle} (demand : request.lookupDemand = some handle)
      (different : Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle ≠
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle)
  | trapped {reason leftCount rightCount}
      (caller : Plain.callerInstance start.store request.thread = .error (.trapped reason))
      (left : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (List.replicate leftCount .tau ++ [.trap reason])
        (StepDefs.trapCfg { start with host := start.host.enter request.name request.kind request.args }))
      (right : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming (List.replicate rightCount .tau ++ [.trap reason]) (StepDefs.trapCfg incoming))
  | refused {issue leftCount rightCount checked canonical}
      (verdict : Plain.runBody request.selectionProgram start.store start.host (some request.thread) =
        (start.store, start.host, .ok (.error issue)))
      (progress : 0 < leftCount)
      (left : ∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start place (List.replicate leftCount .tau) checked place)
      (right : ∀ place, ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming place (List.replicate rightCount .tau) canonical place)
      (paired : HostFrame.Related.Paired older checked canonical)
      (checkedHost : checked.host = (start.host.enter request.name request.kind request.args).record (request.admissionReply issue).1)
      (canonicalHost : canonical.host = incoming.host)
      (tail : RejoinedWorkerTail profile ready bindings callees older checked canonical)
  | admitted {route} (selection : request.Selected route)
      (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted selection.handle = some selection.tree)
      (body : RecursiveGiveDomain selection → ReachedRecursiveGive profile ready callees selection older incoming)

/-- Both paths carry the same occurrence through the actual scheduler
edits. If the mark disappears, an equal segment cannot revive it. -/
def WorkerOccurrencePrefix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (retained : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (mark : Option ReturnFrame.Occurrence.Location)
    (labels : Trace grow sig) (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let base := ComponentCall.hostWithComponent bindings callees
  ∃ reached, Trail profile ready (specDispatch ready base) start mark labels checked reached ∧
    Trail profile ready (specDispatch ready (host bindings base)) incoming mark labels canonical reached ∧
    Outside retained (segmentStorage checked) (segmentStorage canonical) reached ∧
    CoupledOccurrencePaths profile ready base bindings start incoming labels labels checked canonical

/-- The first reached cut in Core execution after a common reply. At a
give installation the canonical side follows the reached live selector;
the baseline tail witnesses only the checked execution. -/
inductive ClassifiedWorkerTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig))
    (track : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop :=
      fun _ _ _ => True) : Prop where
  | complete {other}
      (live : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming labels other)
      (paired : HostFrame.Related.Paired older finish other) (trail : track labels finish other)
  | request {leading label trailing beforeLeft beforeRight afterLeft}
      (split : labels = leading ++ label :: trailing)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start leading beforeLeft)
      (live : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (trail : track leading beforeLeft beforeRight)
      (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) beforeLeft label afterLeft)
      (cut : DirectGiveAt bindings beforeLeft ∨ ∃ request : CoreGiveRequest bindings beforeLeft,
        RecursiveRequestCut profile ready callees request older beforeRight)
      (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) afterLeft trailing finish)
  | boundary {leading label trailing beforeLeft beforeRight afterLeft afterRight}
      (split : labels = leading ++ label :: trailing)
      (checked : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start leading beforeLeft)
      (live : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming leading beforeRight)
      (paired : HostFrame.Related.Paired older beforeLeft beforeRight)
      (trail : track leading beforeLeft beforeRight)
      (boundary : HostFrame.Related.Boundary older beforeLeft beforeRight label afterLeft afterRight)
      (checkedStep : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) beforeLeft label afterLeft)
      (liveStep : Step profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        beforeRight label afterRight)
      (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) afterLeft trailing finish)

/-- Continue from the actual resumed pair. A finite worker prefix can
finish, reach another give, or stop at a genuine open boundary. Older
origins follow the same scheduler steps on each side up to that cut. -/
def RequestWorkerTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request reference : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  ∀ {labels finish}, Steps profile ready (specDispatch ready base) checked labels finish →
    ClassifiedWorkerTail profile ready bindings callees older checked canonical labels finish
      (fun added left right => RequestExitOccurrences profile ready base bindings request reference
        (seen ++ PayloadPrefix.visible added) left right)

/-- The residual run after replay through common ABI refusals. A short
refusal prefix has not reached its reply; the canonical machine is still
at the request. Admitted bodies and open hooks are separate next cuts. -/
inductive WorkerRefusalCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (left right : Config (core3 grow) (HostState sig)) : Trace grow sig → Prop where
  | done : WorkerRefusalCut profile ready bindings callees older left right []
  | boundary {label remaining checked canonical}
      (cut : HostFrame.Related.Boundary older left right label checked canonical)
      (check : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) left label checked)
      (live : Step profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees))) right label canonical) :
      WorkerRefusalCut profile ready bindings callees older left right (label :: remaining)
  | request {label remaining installed}
      (install : GiveInstall bindings (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) left label installed)
      (cut : DirectGiveAt bindings left ∨ ∃ request : CoreGiveRequest bindings left,
        RecursiveRequestCut profile ready callees request older right ∧
        ((∃ handle, request.lookupDemand = some handle ∧
            Stored.Endpoints.Core.childFromHistory left.host.writer.accepted handle ≠
            Stored.Endpoints.Core.childFromHistory right.host.writer.accepted handle) ∨
          (∃ reason, Plain.callerInstance left.store request.thread = .error (.trapped reason)) ∨
          (∃ route, Nonempty (request.Selected route)) ∨
          (∃ issue count replied, (label :: remaining).length < count ∧
            Plain.runBody request.selectionProgram left.store left.host (some request.thread) =
              (left.store, left.host, .ok (.error issue)) ∧
            Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) left
              (List.replicate count .tau) replied))) :
      WorkerRefusalCut profile ready bindings callees older left right (label :: remaining)

/-- Matched worker prefixes reach a paired cut and retain both original
request paths. The residual is still part of the actual checked run. -/
def WorkerRefusalRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request reference : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  ∃ leading canonicalLeading trailing left right,
    labels = leading ++ trailing ∧
    Steps profile ready (specDispatch ready base) checked leading left ∧
    Steps profile ready (specDispatch ready (host bindings base)) canonical canonicalLeading right ∧
    PayloadPrefix.visible canonicalLeading = PayloadPrefix.visible leading ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    HostFrame.Related.Paired older left right ∧
    RequestExitOccurrences profile ready base bindings request reference (seen ++ PayloadPrefix.visible leading) left right ∧
    WorkerRefusalCut profile ready bindings callees older left right trailing

/-- Consume every reached common ABI refusal that finishes within the
supplied finite worker run. -/
def RequestWorkerRefusals (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request reference : Config (core3 grow) (HostState sig)) (seen : Trace grow sig)
    (checked canonical : Config (core3 grow) (HostState sig)) : Prop :=
  ∀ {labels finish}, Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) checked labels finish →
    WorkerRefusalRun profile ready bindings callees older request reference seen checked canonical labels finish

/-- A reached compiler rejection is not a common reply. The checked run
can end before that reply, or it can contain the exact checked handoff.
In the latter case canonical stops at its installed, unexecuted emitter. -/
def CompilerStopSuffix (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings start}
    {route : GiveEffectRoute} (selection : request.Selected route) (issue : Stored.Endpoints.RecordLower.Issue)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin reference incoming : Config (core3 grow) (HostState sig))
    (seen labels : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  ∃ count,
    Steps profile ready (specDispatch ready base) start (List.replicate count .tau) (selection.compilerRefused issue) ∧
    (labels.length < count ∨ ∃ suffix leading entered,
      labels = List.replicate count .tau ++ suffix ∧
      Steps profile ready (specDispatch ready base) (selection.compilerRefused issue) suffix finish ∧
      Steps profile ready (specDispatch ready (host bindings base)) incoming leading entered ∧
      HostFrame.Related.Paired older selection.canonicalPending entered ∧ entered.host = incoming.host ∧
      RequestExitOccurrences profile ready base bindings origin reference seen (selection.compilerRefused issue) entered)

/-- Align a selected body execution with the given checked run. Departure
requires a different reached oracle answer or embedder action and leaves
two separate, actually derived residual paths. -/
inductive WorkerBodyAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (start body : Config (core3 grow) (HostState sig)) (bodyLabels actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | reached {suffix} (split : actual = bodyLabels ++ suffix) (tail : Steps profile ready dispatch body suffix finish)
  | inside {remaining} (split : bodyLabels = actual ++ remaining) (nonempty : remaining ≠ [])
      (remainingBody : Steps profile ready dispatch finish remaining body)
  | departure {leading expected taken rest suffix middle next actualNext}
      (bodySplit : bodyLabels = leading ++ expected :: rest) (actualSplit : actual = leading ++ taken :: suffix)
      (shared : Steps profile ready dispatch start leading middle) (different : expected ≠ taken)
      (branch : workerBranchLabel expected ∧ workerBranchLabel taken)
      (planned : Step profile ready dispatch middle expected next) (bodyTail : Steps profile ready dispatch next rest body)
      (actualStep : Step profile ready dispatch middle taken actualNext) (actualTail : Steps profile ready dispatch actualNext suffix finish)

/-- An aligned machine-local segment. The endpoint is reached only when the
original checked derivation executes the entire segment. -/
inductive LocalRunAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (target : Config (core3 grow) (HostState sig)) (planned actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | reached {residual} (split : actual = planned ++ residual)
      (tail : Steps profile ready dispatch target residual finish)
  | inside {remaining} (split : planned = actual ++ remaining) (nonempty : remaining ≠ [])
      (tail : Steps profile ready dispatch finish remaining target)

/-- Classify a finite run at its last compared field frontier. A prefix
inside a local leaf retains its original suffix without completing the leaf. -/
inductive ElementRunEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig))
    (success : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (refusal : Stored.Endpoints.RecordLower.Issue → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (left right : Config (core3 grow) (HostState sig)) (trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | returned (reached : success left right)
  | refused (issue : Stored.Endpoints.RecordLower.Issue) (reached : refusal issue left right)
  | trapped (checked : left.ctl = []) (canonical : right.ctl = [])
  | inside {remaining target} (nonempty : remaining ≠ [])
      (tail : Steps profile ready (specDispatch ready base) finish remaining target)

def ElementRunSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (success : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (refusal : Stored.Endpoints.RecordLower.Issue → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop)
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checked canonical trailing left right, actual = checked ++ trailing ∧
    PayloadPrefix.visible checked = PayloadPrefix.visible canonical ∧ left.store = right.store ∧
    OccurrenceTransport profile ready base bindings start incoming checked canonical left right ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    ElementRunEnd profile ready base success refusal left right trailing finish

/-- An allocated element sequence ending in the stated output continuations.
On refusal the checked body follows its error arm, while canonical remains
at the exact canonical suffix admitted by the sequence. -/
def AllocatedElementRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    {Result : Type} (checkNext : Except Stored.Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow)))
    (canonNext : Result → Session grow sig (Ret (core3 grow))) (stopsAt : Session grow sig (Ret (core3 grow)) → Prop)
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ElementRunSlice profile ready base bindings
    (fun left right => ∃ value, LinkedCallback.ChildFrameOver older left right check canon ∧
      left.ctl = check.control (checkNext (.ok value)) ∧ right.ctl = canon.control (canonNext value))
    (fun issue left right => left.ctl = check.control (checkNext (.error issue)) ∧
      ∃ stop, stopsAt stop ∧ right.ctl = canon.control stop) start incoming actual finish

/-- Match the actual local descriptor program before exposing a successful
publication or a trap. A checked prefix inside the program cannot advance
the enclosing continuation. -/
def ValueCommitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig)) (output : Stored.Lower.Output)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (published : LinkedCallback.MemorySequence.ValueFinish grow sig output)
    (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open PayloadPrefix in
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason output.Result) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest (fun value => checkNext (.ok value)) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result
    OccurrenceTransport profile ready base bindings left right labels labels lhs rhs ∧
    LocalRunAlignment profile ready (specDispatch ready base) lhs labels actual finish ∧
    ∀ value, result = .ok value → published value lhs rhs check canon

/-- The suffix is the range program (including its marked pop), not a replay
of the checked child or error continuation. -/
def AlignedCollectionRange (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftEntry rightEntry lhs rhs : Config (core3 grow) (HostState sig))
    (checkTrace canonTrace observed actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ leftTail rightTail,
    OccurrenceTransport profile ready base bindings leftEntry rightEntry
      (checkTrace ++ leftTail) (canonTrace ++ rightTail) lhs rhs ∧
    PayloadPrefix.visible leftTail = observed ∧ PayloadPrefix.visible rightTail = observed ∧ lhs.store = rhs.store ∧
    LocalRunAlignment profile ready (specDispatch ready base) lhs leftTail actual finish

/-- The concrete checked verdict chooses the reached continuation. A range
trap does not enter that continuation; a refusal leaves the peer at its
canonical child entry. -/
def CollectionRangeRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (leftEntry rightEntry checked canonical : Config (core3 grow) (HostState sig))
    (checkTrace canonTrace actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (destination : RecordDestination) (area : ABI.Layout) (count pointer : Nat)
    (plan : List Stored.Endpoints.RecordLower.Object)
    (checkNext : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow))) : Prop :=
  let trap := fun reason => AlignedCollectionRange profile ready base bindings leftEntry rightEntry
    (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) checkTrace canonTrace [.trap reason] actual finish
  ∃ bytes, (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
        let verdict := OwnedMemory.Claims.Record.prepare checked.store checked.host.writer plan
        let lhs := { checked with ctl := cursor.control (checkNext pointer verdict) }
        let rhs := { canonical with ctl := canon.control (canonNext pointer) }
        LinkedCallback.ChildFrameOver older lhs rhs cursor canon ∧
        AlignedCollectionRange profile ready base bindings leftEntry rightEntry lhs rhs checkTrace canonTrace [] actual finish
    else trap .outOfBounds

/-- Cut the collection field's original derivation at the install, callback,
or range frontier. The actual callback traces and peer are retained even
when no returning range path can be entered. -/
def CollectionRunSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output)
    (canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output)
    (start incoming : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (before : Trace grow sig) (visit : Nat → Nat → TrailFinish grow sig) : Prop :=
  open PayloadPrefix Stored.Endpoints.RecordLower ReturnFrame.Occurrence in
  match OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) with
  | .error issue =>
    let refusal := match issue with
      | .preflight reason => Issue.field index (.beforeAllocation reason)
      | reason => Issue.nested index reason
    let stopped := { start with ctl := check.control (checkNext (.error refusal)) }
    OccurrenceTransport profile ready base bindings start incoming [.tau, .tau] [] stopped incoming ∧
    LocalRunAlignment profile ready (specDispatch ready base) stopped [.tau, .tau] actual finish
  | .ok () =>
    let area := ABI.layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext mode
    let leftEntry := collectionEntry destination inst area entries.length (specDispatch ready base) start check first
    let rightEntry := collectionEntry destination inst area entries.length
      (specDispatch ready (LiveDispatch.host bindings base)) incoming canon second
    actual.length < 3 ∨ ∃ checked canonical trailing reached peer mark,
      let checkTrace := [.tau, .tau, .tau] ++ checked
      let canonTrace := [.tau, .tau] ++ canonical
      actual = checkTrace ++ trailing ∧
      PayloadPrefix.visible canonical = PayloadPrefix.visible checked ∧
      AllocatorMark profile ready base bindings older leftEntry rightEntry checked canonical reached peer mark ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached peer ∧
      OccurrenceTransport profile ready base bindings start incoming checkTrace canonTrace reached peer [mark] ∧
      CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend older first second) reached peer trailing finish ∧
      ((trailing = [] ∨ mark ≠ some (.active 0 0) ∨
        ¬ ∃ (pointer : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)),
          reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer))) ∨
        ∃ (pointer : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)) (residual : Trace grow sig),
          mark = some (.active 0 0) ∧ trailing = .tau :: residual ∧
          reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) ∧
          Steps profile ready (specDispatch ready base) { reached with ctl := cursor.control (first (.nat pointer)) } residual finish ∧
          CollectionRangeRun profile ready base bindings older start incoming reached peer checkTrace canonTrace trailing finish
            cursor destination area entries.length pointer (Field.listObjects entries)
            (fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
            (fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) ∧
          (∀ bytes, (core3 grow).memSize? reached.store.core destination.memory = some bytes →
            pointer = ABI.alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
            OwnedMemory.Claims.Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .ok () →
            ∃ lhs rhs peerCursor, LinkedCallback.ChildFrameOver older lhs rhs cursor peerCursor ∧
              (core3 grow).memAddrType? lhs.store.core destination.memory = some destination.width ∧
              (core3 grow).memSize? lhs.store.core destination.memory = some bytes ∧
              Core3.Grows start.store.core lhs.store.core ∧
              lhs.ctl = cursor.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) ∧
              rhs.ctl = peerCursor.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) ∧
              AlignedCollectionRange profile ready base bindings start incoming lhs rhs checkTrace canonTrace [] trailing finish ∧
              visit pointer bytes (before ++ PayloadPrefix.visible checked) lhs rhs cursor peerCursor))

/-- The observed return focus is not itself an executed pop. Only the
matched case advances both continuations and exposes an actual shorter
checked residual. A displaced or lost mark cannot authorize this pop. -/
def ActualMarkedPop (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checkEntry canonEntry left right : Config (core3 grow) (HostState sig)) (checkTrace canonTrace : Trace grow sig)
    (mark : Option ReturnFrame.Occurrence.Location) (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) (value : Ret (core3 grow))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  mark ≠ some (.active 0 0) ∨ (actual = [] ∧ finish = left) ∨
    ∃ (trailing : Trace grow sig) (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
      let resumed := { left with ctl := check.control (first value) }
      let peer := { right with ctl := canon.control (second value) }
      mark = some (.active 0 0) ∧ actual = .tau :: trailing ∧ trailing.length < actual.length ∧
      Steps profile ready (specDispatch ready base) resumed trailing finish ∧
      Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) right .tau peer ∧
      LinkedCallback.ChildFrameOver older left right check canon ∧
      CoupledOccurrencePaths profile ready base bindings checkEntry canonEntry (checkTrace ++ [.tau]) (canonTrace ++ [.tau]) resumed peer ∧
      ∀ {leftStart rightStart : Config (core3 grow) (HostState sig)} {leftLabels rightLabels : Trace grow sig},
        ∀ {enclosing : List (Option ReturnFrame.Occurrence.Location)},
        OccurrenceTransport profile ready base bindings leftStart rightStart leftLabels rightLabels left right
          (some (.active 0 0) :: enclosing) →
        OccurrenceTransport profile ready base bindings leftStart rightStart (leftLabels ++ [.tau]) (rightLabels ++ [.tau]) resumed peer
          (enclosing.map (fun place => place.bind (ReturnFrame.Occurrence.Edit.pop : ReturnFrame.Occurrence.Edit (core3 grow) (HostState sig)).follow))

/-- Compare the actual suffix of a reached cancellation-hook installation.
The installed occurrence can be lost or displaced; only its executed pop
enters the checked continuation, even if an equal hook frame is in focus. -/
def CancelHookCallbackSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (checked canonical : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  (actual = [] ∧ finish = checked) ∨
    ∃ checkEntry canonEntry checkLabels canonLabels trailing reached peer mark,
      actual = .tau :: (checkLabels ++ trailing) ∧
      OccurrenceTransport profile ready base bindings checked canonical [.tau] [.tau] checkEntry canonEntry [some (.active 0 0)] ∧
      OccurrenceTransport profile ready base bindings checked canonical (.tau :: checkLabels) (.tau :: canonLabels) reached peer [mark] ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
      AllocatorMark profile ready base bindings older checkEntry canonEntry checkLabels canonLabels reached peer mark ∧
      CallbackSliceEnd profile ready base bindings (ReturnFrame.Extend older resume resume) reached peer trailing finish ∧
      ∀ value (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
        reached.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (.pure value) →
        ActualMarkedPop profile ready base bindings older checkEntry canonEntry reached peer checkLabels canonLabels
          mark cursor resume resume value trailing finish

/-- Track the caller installed at the start of a component result path.
Resolution alone leaves the reply in focus. Only the checked residual's actual
pop of that occurrence can consume it; a missing or displaced mark cannot. -/
def ComponentMarkedReplyTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming reached peer : Config (core3 grow) (HostState sig)) (leading : Trace grow sig)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (suffix : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ mark, AllocatorMark profile ready base bindings older start incoming leading leading reached peer mark ∧
    (reached.ctl = check.control (.pure (.cancel .none)) →
      mark ≠ some (.active 0 0) ∨ ∃ after : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
        check = { after with frames := .prog first :: after.frames } ∧
        ActualMarkedPop profile ready base bindings older start incoming reached peer leading leading mark
          after first second (.cancel .none) suffix finish)

/-- Immediately after the admitted entry's final arena read, with this side's
own ticket and live child-selection result. -/
def componentPreflightAt (callee : ComponentCall.Callee sig) (caller : CallerId)
    (cx : LiftLowerContext (core3 grow)) (args : List FlatValue)
    (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) :
    Config (core3 grow) (HostState sig) :=
  { state with
    host := state.host.enter callee.name callee.coreType args
    ctl := cursor.control (ComponentCall.acceptCaller callee caller state.host.nextTicket state.host.writer.accepted state.store cx args) }

/-- The observation used by the reached registration probe. A refused registration
does not read a handle, and exhaustion does not use the out-of-range index. -/
inductive ComponentRegistration where
  | aliased
  | exhausted
  | fresh (handle : Nat)

def componentRegistration (writer : Stored.OwnedMemory.Claims.State sig) (tree : Stored.OwnedMemory.Tree sig) :
    ComponentRegistration :=
  match writer.register tree with
  | .error _ => .aliased
  | .ok registered => if registered.accepted.length ≥ 2 ^ 32 then .exhausted else .fresh registered.accepted.length

def componentRegistrationProgram (ticket : Nat) (caller : CallerId) (tree : Stored.OwnedMemory.Tree sig) :
    ComponentRegistration → Session grow sig (Ret (core3 grow))
  | .aliased => ComponentCall.resolveRefused ticket caller (.accept (.claims .alias))
  | .exhausted => ComponentCall.reject ticket (.accept (.boundary .exhaustedHandles))
  | .fresh handle => do
    lowerOnResolve Limits.spec Quirks.none caller (some [.variant 0 (some (Value.Val.u32 handle))])
    ComponentCall.completeResolvedTree ticket tree handle

/-- A mismatch is at the actual registration-read continuations, not at an
unvalidated payload or an assumed disagreement of whole writer states. -/
inductive ComponentObservedAcceptance (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (callee : ComponentCall.Callee sig) (caller : CallerId) (leftTicket rightTicket : Nat)
    (planned : Option (List (Stored.OwnedMemory.Tree sig)))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (start incoming reached peer : Config (core3 grow) (HostState sig)) (leading suffix : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | pending (exhausted : suffix = []) (paired : PairedComponentSite wider reached peer check canon)
  | trapped (checked : reached.ctl = []) (canonical : peer.ctl = [])
      (paired : HostFrame.Related.Paired wider reached peer)
  | registrationMismatch {tree : Stored.OwnedMemory.Tree sig}
      (checked : reached.ctl = check.control (componentRegistrationProgram leftTicket caller tree
        (componentRegistration reached.host.writer tree)))
      (canonical : peer.ctl = canon.control (componentRegistrationProgram rightTicket caller tree
        (componentRegistration peer.host.writer tree)))
      (paired : PairedComponentSite wider reached peer check canon)
      (mismatch : componentRegistration reached.host.writer tree ≠ componentRegistration peer.host.writer tree)
  | refused
      (frontier : ComponentStoreFrontier (Result := Unit) wider check canon
        (fun _ => .pure (.cancel .none)) (fun _ => .pure (.cancel .none)) reached peer suffix True)
      (reply : ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
        check first second suffix finish)
  | accepted {tree handle}
      (frontier : ComponentAcceptedFrontier wider check canon tree handle reached peer suffix)
      (reply : ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
        check first second suffix finish)

/-- The classification after the admitted entry reaches child preflight.
Disagreement is on the demanded decision, not on the complete journals.
Each common decision consumes the checked residual from this exact site. -/
def ComponentPreflightTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (callee : ComponentCall.Callee sig) (caller : CallerId) (leftTicket rightTicket : Nat)
    (leftPlan rightPlan : Except Scheduled.Issue (Option (List (Stored.OwnedMemory.Tree sig))))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  leftPlan ≠ rightPlan ∨ ∃ plan, leftPlan = plan ∧ rightPlan = plan ∧
    match plan with
    | .error _ =>
      ComponentEarlyPrefix profile ready base bindings wider check canon start incoming labels finish 7 ∨
      ∃ leading suffix reached peer, labels = leading ++ suffix ∧
        OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
        Steps profile ready (specDispatch ready base) reached suffix finish ∧
        ComponentStoreFrontier (Result := Unit) wider check canon (fun _ => .pure (.cancel .none))
          (fun _ => .pure (.cancel .none)) reached peer suffix True ∧
        ComponentMarkedReplyTail profile ready base bindings older start incoming reached peer leading
          check first second suffix finish
    | .ok planned =>
      ∃ leading suffix reached peer, labels = leading ++ suffix ∧
        OccurrenceTransport profile ready base bindings start incoming leading leading reached peer ∧
        Steps profile ready (specDispatch ready base) reached suffix finish ∧
        ComponentObservedAcceptance profile ready base bindings older wider callee caller leftTicket rightTicket
          planned check canon first second start incoming reached peer leading suffix finish

/-- The finite body cut starts at the installed component invocation. The
seven-step entry is consumed only if present in the actual checked run. -/
def ComponentAdmissionCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (callee : ComponentCall.Callee sig) (caller : CallerId) (cx : LiftLowerContext (core3 grow)) (args : List FlatValue)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  (∃ canon, ComponentEarlyPrefix profile ready base bindings wider check canon start incoming labels finish 7) ∨
  ∃ peerFrames peerRest suffix,
    let canon := { check with frames := peerFrames, rest := peerRest }
    let reached := componentPreflightAt callee caller cx args start check
    let peer := componentPreflightAt callee caller cx args incoming canon
    labels = List.replicate 7 .tau ++ suffix ∧
    OccurrenceTransport profile ready base bindings start incoming (List.replicate 7 .tau) (List.replicate 7 .tau) reached peer ∧
    Steps profile ready (specDispatch ready base) reached suffix finish ∧
    PairedComponentSite wider reached peer check canon ∧
    ComponentPreflightTail profile ready base bindings older wider callee caller start.host.nextTicket incoming.host.nextTicket
      (callee.childPreflight start.host.writer.accepted start.store cx args)
      (callee.childPreflight incoming.host.writer.accepted incoming.store cx args)
      check canon first second reached peer suffix finish

/-- The positive dispatch and admission branch, inspected at the actual call
site. Failure of this predicate is a frontier, not a synthetic runtime reply. -/
def ComponentHostAdmission (callees : List (ComponentCall.Callee sig)) (hostId : HostFuncId) (caller : CallerId)
    (active : ThreadId) (state : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ callee subtask cx args pos ft limits results entry task,
    callees.filter (·.hostId == hostId) = [callee] ∧
    ArenaField.callers.get? state.store caller = some (.lower subtask cx args pos ft limits results) ∧
    ArenaField.threads.get? state.store active = some entry ∧
    ArenaField.tasks.get? state.store entry.task = some task ∧ task.inst = callee.inst ∧
    callee.check state.store subtask cx args pos ft (limits, results) = .ok ()

/-- A failed link or admission follows the executed dispatcher through any
entry and diagnostic writes. An exhausted prefix may precede lockdown;
neither outcome claims an original caller pop. -/
def ComponentEntryFailure (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming finish : Config (core3 grow) (HostState sig))
    (label : Label (core3 grow) (HostState sig)) (trailing : Trace grow sig) : Prop :=
  let base := ComponentCall.hostWithComponent (grow := grow) bindings callees
  ∃ leading suffix reached peer check canon,
    label = .tau ∧ trailing = leading ++ suffix ∧
    OccurrenceTransport profile ready base bindings start incoming (.tau :: leading) (.tau :: leading) reached peer ∧
    Steps profile ready (specDispatch ready base) reached suffix finish ∧
    ((suffix = [] ∧ PairedComponentSite older reached peer check canon) ∨
      (reached.ctl = [] ∧ peer.ctl = [] ∧ HostFrame.Related.Paired older reached peer))

/-- Classify nominal linkage separately from the linked caller's admission.
Both failures carry their executed prefixes, not synthetic caller replies. -/
def ComponentInstallOutcome (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (before incoming next finish : Config (core3 grow) (HostState sig)) (label : Label (core3 grow) (HostState sig))
    (trailing : Trace grow sig) : Prop :=
  ∀ active hostId caller resume frames rest,
    before.ctl = ⟨some active, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest →
    ((∃ callee, callees.filter (·.hostId == hostId) = [callee]) ∧
      ¬ ComponentHostAdmission callees hostId caller active before ∧
      ComponentEntryFailure profile ready bindings callees older before incoming finish label trailing) ∨
    ((¬ ∃ callee, callees.filter (·.hostId == hostId) = [callee]) ∧
      ComponentEntryFailure profile ready bindings callees older before incoming finish label trailing) ∨
    ∃ callee cx args peerFrames peerRest,
      let base := ComponentCall.hostWithComponent (grow := grow) bindings callees
      let peer := { incoming with ctl := ⟨some active, .prog (ComponentCall.invoke callee caller), .prog resume :: peerFrames⟩ :: peerRest }
      callees.filter (·.hostId == hostId) = [callee] ∧ label = .tau ∧
      OccurrenceTransport profile ready base bindings before incoming [.tau] [.tau] next peer [some (.active 0 0)] ∧
      ComponentAdmissionCut profile ready base bindings older older callee caller cx args
        ⟨some active, .prog resume :: frames, rest⟩ resume resume next peer trailing finish

/-- The worker prefix is paired until its first boundary. A component install
uses the boundary's exact checked step and suffix to classify the admitted body. -/
inductive ComponentWorkerCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop where
  | complete {peer} (segment : ExecutedCallbackSegment profile ready (ComponentCall.hostWithComponent bindings callees)
      bindings older start incoming labels labels finish peer)
  | boundary {leading label trailing reached peer next}
      (split : labels = leading ++ label :: trailing)
      (segment : ExecutedCallbackSegment profile ready (ComponentCall.hostWithComponent bindings callees)
        bindings older start incoming leading leading reached peer)
      (kind : CallbackWorkerBoundary bindings ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        (fun resume => ∃ other, older resume other) reached label next)
      (step : Step profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) reached label next)
      (tail : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) next trailing finish)
      (smaller : trailing.length < labels.length)
      (installed : ComponentInstallOutcome profile ready bindings callees older reached peer next finish label trailing)

/-- An actual finite mixed worker prefix under the fixed component dispatcher.
The residual retains its exact first step and tail; if it is a component
install, the live dispatch/admission classification is at that same site. -/
def MixedCallbackSlice (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming : Config (core3 grow) (HostState sig)) (labels : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent (grow := grow) bindings callees
  ∃ checked canonical trailing reached peer,
    labels = checked ++ trailing ∧
    ExecutedCallbackSegment profile ready base bindings older start incoming checked canonical reached peer ∧
    CallbackSliceEnd profile ready base bindings older reached peer trailing finish ∧
    ((trailing = [] ∧ finish = reached) ∨
      ∃ label rest next, trailing = label :: rest ∧
        Step profile ready (specDispatch ready base) reached label next ∧
        Steps profile ready (specDispatch ready base) next rest finish ∧
        ComponentInstallOutcome profile ready bindings callees older reached peer next finish label rest)

/-- Consume the actual post-pop worker run, when reached. A different resumed
program is an explicit boundary, not a replay or a runtime refusal. -/
def ComponentMarkedWorkerTail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (start incoming reached peer : Config (core3 grow) (HostState sig)) (leading : Trace grow sig)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (suffix : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  reached.ctl ≠ check.control (.pure (.cancel .none)) ∨
  (∃ mark, AllocatorMark profile ready base bindings older start incoming leading leading reached peer mark ∧
    mark ≠ some (.active 0 0)) ∨ (suffix = [] ∧ finish = reached) ∨
  ∃ (remaining : Trace grow sig) (after canonAfter : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
    let resumed := { reached with ctl := after.control (first (.cancel .none)) }
    let canon := { peer with ctl := canonAfter.control (second (.cancel .none)) }
    suffix = .tau :: remaining ∧ remaining.length < suffix.length ∧
    Steps profile ready (specDispatch ready base) resumed remaining finish ∧
    OccurrenceTransport profile ready base bindings start incoming (leading ++ [.tau]) (leading ++ [.tau]) resumed canon ∧
    (first (.cancel .none) ≠ second (.cancel .none) ∨
      ∃ checked canonical trailing worker workerPeer,
        remaining = checked ++ trailing ∧
        OccurrenceTransport profile ready base bindings start incoming
          ((leading ++ [.tau]) ++ checked) ((leading ++ [.tau]) ++ canonical) worker workerPeer ∧
        PayloadPrefix.visible canonical = PayloadPrefix.visible checked ∧
        CallbackSliceEnd profile ready base bindings older worker workerPeer trailing finish)

/-- Compare the checked run with the entry obtained from the real public
guards. A short run need not have taken the displayed refusal or trap. -/
inductive RecursiveRootEntryAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | refused {issue leading} (silent : PayloadPrefix.visible leading = [])
      (checked : ∀ place, ReturnFrame.Occurrence.Trail profile ready
        (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start (some place) (leading ++ [.tau, .tau, .tau]) (site.refusedReply issue) (some place))
      (aligned : WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start (site.refusedReply issue) (leading ++ [.tau, .tau, .tau]) actual finish)
  | placementTrap {reason count}
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .error reason)
      (checked : site.EntryTrap profile ready (ComponentCall.hostWithComponent bindings callees)
        (List.replicate count .tau ++ [.trap reason]))
      (aligned : WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start (StepDefs.trapCfg site.checked) (List.replicate count .tau ++ [.trap reason]) actual finish)
  | placed {leading} (silent : PayloadPrefix.visible leading = [])
      (verdict : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
      (prepared : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
      (checked : site.EntryPrefix profile ready (ComponentCall.hostWithComponent bindings callees) leading site.checked)
      (body : RecursiveGiveOccurrencePaths profile ready bindings callees older incoming route site)
      (aligned : WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        site.start site.checked leading actual finish)

/-- The actual checked residual of a selected give enters the compiler or
root cut only if the finite execution covers that entry. The canonical
pending state is not an error reply or a finished body. -/
inductive RecursiveGiveEntryAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings start}
    {route : GiveEffectRoute} (selection : request.Selected route)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | compilerRefused {issue count entered} (preflight : selection.preflight = .error issue)
      (pending : HostFrame.Related.Paired older selection.canonicalPending entered)
      (occurrences : RequestExitOccurrences profile ready (ComponentCall.hostWithComponent bindings callees)
        bindings start incoming [] (selection.compilerRefused issue) entered)
      (aligned : WorkerBodyAlignment profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (selection.compilerRefused issue) (List.replicate count .tau) actual finish)
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (pending : PendingRecursiveRoot profile ready bindings callees older (selection.site tag payload arity children field) incoming)
      (aligned : RecursiveRootEntryAlignment profile ready bindings callees older incoming
        (selection.site tag payload arity children field) actual finish)

/-- Replay the closed part of the actual suffix after a common public reply.
A further give is classified at its reached pair, with the real checked
installation and tail. The suffix transports enclosing occurrences across
the closed steps, but does not replay any open action or protected pop. -/
def RejoinedCallbackReplay (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request reference checked canonical : Config (core3 grow) (HostState sig))
    (checkPrefix canonPrefix actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  let base := ComponentCall.hostWithComponent bindings callees
  let dispatch := specDispatch ready base
  ∃ leading remaining lhs rhs,
    actual = leading ++ remaining ∧ Steps profile ready dispatch checked leading lhs ∧
    Steps profile ready (specDispatch ready (host bindings base)) canonical leading rhs ∧
    HostFrame.Related.Paired older lhs rhs ∧
    CoupledOccurrencePaths profile ready base bindings request reference (checkPrefix ++ leading) (canonPrefix ++ leading) lhs rhs ∧
    OccurrenceTransport profile ready base bindings checked canonical leading leading lhs rhs ∧
    ((remaining = [] ∧ lhs = finish) ∨
      ∃ label tail next, remaining = label :: tail ∧ Step profile ready dispatch lhs label next ∧
        Steps profile ready dispatch next tail finish ∧
        CallbackWorkerBoundary bindings ready dispatch (fun resume => ∃ peer, older resume peer) lhs label next ∧
        (GiveInstall bindings dispatch lhs label next →
          DirectGiveAt bindings lhs ∨ ∃ req : CoreGiveRequest bindings lhs, RecursiveRequestCut profile ready callees req older rhs))

/-- Compare the derived successful body with the actual finite worker run.
A different scheduler branch, an unfinished body, or a missing original
caller does not authorize a reply. After an executed pop, only the actual
shorter residual can drive the next dispatch. -/
def PublicTransportWorkerAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (incoming left right : Config (core3 grow) (HostState sig))
    (checkEntry canonEntry seen actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let base := ComponentCall.hostWithComponent bindings callees
  let dispatch := specDispatch ready base
  ∃ (checkBody canonBody : Trace grow sig) (mark : Option Location),
    PayloadPrefix.visible checkBody = seen ∧ PayloadPrefix.visible canonBody = seen ∧
    OccurrenceTransport profile ready base bindings site.start incoming (checkEntry ++ checkBody) (canonEntry ++ canonBody)
      left right [mark] ∧
    WorkerBodyAlignment profile ready dispatch site.start left (checkEntry ++ checkBody) actual finish ∧
    ∀ tail, actual = (checkEntry ++ checkBody) ++ tail → Steps profile ready dispatch left tail finish →
      mark = some (.active 0 0) →
      tail.length < 3 ∨ ∃ suffix checked canonical,
        tail = [.tau, .tau, .tau] ++ suffix ∧ suffix.length < actual.length ∧
        Steps profile ready dispatch checked suffix finish ∧ HostFrame.Related.Paired older checked canonical ∧
        OccurrenceTransport profile ready base bindings site.start incoming
          ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) ((canonEntry ++ canonBody) ++ [.tau]) checked canonical ∧
        RejoinedWorkerTail profile ready bindings callees older checked canonical ∧
        RejoinedCallbackReplay profile ready bindings callees older site.start incoming checked canonical
          ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) ((canonEntry ++ canonBody) ++ [.tau]) suffix finish ∧
        (PayloadPrefix.visible checkEntry = PayloadPrefix.visible canonEntry →
          ExecutedCallbackSegment profile ready base bindings older site.start incoming
            ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) ((canonEntry ++ canonBody) ++ [.tau]) checked canonical ∨
          ReachedNonGrowingUpdate profile ready dispatch site.start ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]) checked) ∧
        ∀ {retained enclosingLeft enclosingRight leftTrace rightTrace cursor},
          AllocatorMark profile ready base bindings retained enclosingLeft enclosingRight leftTrace rightTrace site.start incoming cursor →
          ∃ reached,
            AllocatorMark profile ready base bindings retained enclosingLeft enclosingRight
              (leftTrace ++ ((checkEntry ++ checkBody) ++ [.tau, .tau, .tau]))
              (rightTrace ++ ((canonEntry ++ canonBody) ++ [.tau])) checked canonical reached ∧
            ClassifiedWorkerTail profile ready bindings callees older checked canonical suffix finish
              (WorkerOccurrencePrefix profile ready bindings callees retained checked canonical reached)

/-- Match an actual checked run against a marked public body endpoint.
Only an executed reply pop supplies a worker suffix. A common return carries
the same older occurrence coordinates through both replies, including loss;
a typed reply does not authorize a canonical pop or suffix. -/
def PublicGiveWorkerAlignment (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (entered left right : Config (core3 grow) (HostState sig))
    (verdict : Except Stored.Endpoints.RecordLower.Issue route.output.Result)
    (origin reference incoming : Config (core3 grow) (HostState sig))
    (entryLabels canonEntryLabels prior seen actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let base := ComponentCall.hostWithComponent bindings callees
  let dispatch := specDispatch ready base
  ∃ bodyLabels canonLabels mark,
    Trail profile ready dispatch site.checked (some (.active 0 0)) bodyLabels left mark ∧
    Trail profile ready (specDispatch ready (host bindings base)) entered (some (.active 0 0)) canonLabels right mark ∧
    RequestExitOccurrences profile ready base bindings origin reference (prior ++ seen) left right ∧
    WorkerBodyAlignment profile ready dispatch site.start left (entryLabels ++ bodyLabels) actual finish ∧
    ∀ tail, actual = (entryLabels ++ bodyLabels) ++ tail → Steps profile ready dispatch left tail finish →
      mark = some (.active 0 0) →
      tail.length < 3 ∨ ∃ suffix checked canonical,
        tail = [.tau, .tau, .tau] ++ suffix ∧ suffix.length < actual.length ∧
        Steps profile ready dispatch checked suffix finish ∧
        RequestExitOccurrences profile ready base bindings origin reference (prior ++ seen) checked canonical ∧
        match verdict with
        | .error _ => canonical = right
        | .ok _ => HostFrame.Related.Paired older checked canonical ∧
          CoupledOccurrencePaths profile ready base bindings site.start incoming
            ((entryLabels ++ bodyLabels) ++ [.tau, .tau, .tau]) ((canonEntryLabels ++ canonLabels) ++ [.tau]) checked canonical ∧
          RejoinedCallbackReplay profile ready bindings callees older site.start incoming checked canonical
            ((entryLabels ++ bodyLabels) ++ [.tau, .tau, .tau]) ((canonEntryLabels ++ canonLabels) ++ [.tau]) suffix finish ∧
          WorkerRefusalRun profile ready bindings callees older origin reference (prior ++ seen) checked canonical suffix finish

/-- Use the checked run from the original request at each reached success
or late typed refusal. The refused branch advances only checked execution
and keeps the reached canonical body endpoint. -/
def LinkedMemoryWorkerBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedMemoryTransportBodyWith profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
    (fun checkEntry canonEntry _ seen left right =>
      PublicTransportWorkerAlignment profile ready bindings callees older site incoming left right checkEntry canonEntry seen actual finish)
    (fun checkEntry canonEntry entered issue seen left right => PayloadPrefix.visible checkEntry = [] →
      PublicGiveWorkerAlignment profile ready bindings callees older site entered left right (.error issue)
        site.start incoming incoming checkEntry canonEntry [] seen actual finish)

/-- The real checked worker suffix at the flat public boundary. A late
refusal does not share its checked reply with the stopped canonical run. -/
def LinkedFlatWorkerBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {type : Stored.TypeOf}
    (site : PayloadRoot.Site grow sig (.flat type)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  LinkedFlatTransportBodyWith profile ready (ComponentCall.hostWithComponent bindings callees) bindings older site incoming
    (fun checkEntry canonEntry entered words seen left right =>
      PublicSuccessTransport profile ready (ComponentCall.hostWithComponent bindings callees) bindings older
        site incoming entered checkEntry canonEntry words seen left right ∧
      PublicTransportWorkerAlignment profile ready bindings callees older site incoming left right checkEntry canonEntry seen actual finish)
    (fun checkEntry canonEntry entered issue seen left right => PayloadPrefix.visible checkEntry = [] →
      PublicGiveWorkerAlignment profile ready bindings callees older site entered left right (.error issue)
        site.start incoming incoming checkEntry canonEntry [] seen actual finish)

/-- The recursive visitor and its actual worker observations for the ABI
selected at a reached public request. -/
def RecursiveWorkerBody (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : (route : GiveEffectRoute) → PayloadRoot.Site grow sig route → Prop
  | .memory _, site => LinkedMemoryWorkerBody profile ready bindings callees older site incoming actual finish
  | .flat _, site => LinkedFlatWorkerBody profile ready bindings callees older site incoming actual finish

/-- Classify the compiled route at the executed installation, not at a
separately chosen callback run. Refusing compilation leaves the reached
canonical continuation pending. -/
inductive ActualSelectedGive (profile : ProfileKind) (ready : HostReady (HostState sig))
    (callees : List (ComponentCall.Callee sig)) {bindings : List (Binding sig)}
    {start : Config (core3 grow) (HostState sig)} {request : CoreGiveRequest bindings start}
    {route : GiveEffectRoute} (selection : request.Selected route)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop where
  | compilerRefused {issue} (preflight : selection.preflight = .error issue)
      (cut : RecursiveGiveEntryAlignment profile ready callees selection older incoming actual finish)
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (cut : PayloadRoot.Cut (selection.site tag payload arity children field) profile ready bindings
        (RecursiveWorkerBody profile ready bindings callees older incoming actual finish route
          (selection.site tag payload arity children field)) (ComponentCall.hostWithComponent bindings callees))
      (entry : RecursiveGiveEntryAlignment profile ready callees selection older incoming actual finish)

/-- After a common nested reply, follow the closed part of its actual
residual up to the next boundary. Only the original allocator occurrence
can authorize its pop, and only an executed pop exposes a new residual. -/
def RejoinedAllocatorResidual (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (callees : List (ComponentCall.Callee sig))
    (retained : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (checkEntry canonEntry checked canonical : Config (core3 grow) (HostState sig))
    (checkTrace canonTrace actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  let base := ComponentCall.hostWithComponent bindings callees
  ∃ leading remaining lhs rhs mark,
    actual = leading ++ remaining ∧
    Steps profile ready (specDispatch ready base) checked leading lhs ∧
    Steps profile ready (specDispatch ready (host bindings base)) canonical leading rhs ∧
    Steps profile ready (specDispatch ready base) lhs remaining finish ∧
    AllocatorMark profile ready base bindings retained checkEntry canonEntry
      (checkTrace ++ leading) (canonTrace ++ leading) lhs rhs mark ∧
    ∀ value (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
      lhs.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure value) →
      ActualMarkedPop profile ready base bindings retained checkEntry canonEntry lhs rhs
        (checkTrace ++ leading) (canonTrace ++ leading) mark cursor first second value remaining finish

/-- Compiled memory fragment consumed by the finite visitor. Compound nodes
carry layout evidence and the shapes of their active children. This is a
proof domain, not a runtime check for support. -/
inductive MemoryVisitShape : Stored.Endpoints.RecordLower.Field → Prop where
  | handle {item} : CanonicalHandle item → MemoryVisitShape item
  | scalar {type} {payload : Stored.Payload type} : PayloadPrefix.LocalDataType type → MemoryVisitShape (.data type payload)
  | string {item} : item.LayoutMatches (.prim .string) → item.Emitted → MemoryVisitShape item
  | aggregate {type items} : Stored.Endpoints.RecordLower.Field.LayoutMatches (.aggregate type items) type →
      (∀ item ∈ items, MemoryVisitShape item) → MemoryVisitShape (.aggregate type items)
  | fixed {element length entries} : entries.length = length →
      Stored.Endpoints.RecordLower.Field.EntriesMatch entries element →
      (∀ item ∈ entries, MemoryVisitShape item) → MemoryVisitShape (.fixed element length entries)
  | sum {type arms tag selected} :
      (∀ width, ABI.layout width type = ABI.variantLayout (arms.map (ABI.layoutOption width))) →
      (∀ item, selected = some item → some item.type ∈ arms) →
      (∀ item, selected = some item → MemoryVisitShape item) →
      MemoryVisitShape (.sum type arms tag selected)
  | list {element entries} : Stored.Endpoints.RecordLower.Field.EntriesMatch entries element →
      (∀ item ∈ entries, MemoryVisitShape item) → MemoryVisitShape (.dynamic (.list element) element entries)
  | map {key element entries} :
      Stored.Endpoints.RecordLower.Field.EntriesMatch entries (.record (ABI.mapEntryFields key element)) →
      Stored.Endpoints.RecordLower.Field.Emitted (.dynamic (.map key element) (.record (ABI.mapEntryFields key element)) entries) →
      (∀ keyField value, Stored.Endpoints.RecordLower.Field.aggregate (.record (ABI.mapEntryFields key element)) [keyField, value] ∈ entries →
        ∀ child ∈ [keyField, value], MemoryVisitShape child) →
      MemoryVisitShape (.dynamic (.map key element) (.record (ABI.mapEntryFields key element)) entries)

/-- Flat leaves, aggregates, fixed arrays, dynamic collections with placed entries and selected sums.
This is a proof domain, not a runtime check for support. -/
inductive FlatVisitShape : Stored.Endpoints.RecordLower.Field → Prop where
  | handle (item : Stored.Endpoints.RecordLower.Field) (nominal : CanonicalHandle item) : FlatVisitShape item
  | scalar (type : Stored.TypeOf) (data : PayloadPrefix.LocalDataType type) (payload : Stored.Payload type) :
      FlatVisitShape (.data type payload)
  | string (item : Stored.Endpoints.RecordLower.Field) (matched : item.LayoutMatches (.prim .string))
      (emitted : item.Emitted) : FlatVisitShape item
  | aggregate (type : Stored.TypeOf) (fields : List Stored.Endpoints.RecordLower.Field)
      (children : ∀ field ∈ fields, FlatVisitShape field) : FlatVisitShape (.aggregate type fields)
  | fixed (element : Stored.TypeOf) (length : Nat) (items : List Stored.Endpoints.RecordLower.Field)
      (children : ∀ field ∈ items, FlatVisitShape field) : FlatVisitShape (.fixed element length items)
  | collection (type element : Stored.TypeOf) (entries : List Stored.Endpoints.RecordLower.Field)
      (matching : Stored.Endpoints.RecordLower.Field.EntriesMatch entries element)
      (children : ∀ field ∈ entries, MemoryVisitShape field) : FlatVisitShape (.dynamic type element entries)
  | sum (type : Stored.TypeOf) (arms : List (Option Stored.TypeOf)) (tag : Nat)
      (selected : Option Stored.Endpoints.RecordLower.Field)
      (matched : Stored.Endpoints.RecordLower.Field.LayoutMatches (.sum type arms tag selected) type)
      (child : ∀ field, selected = some field → FlatVisitShape field) : FlatVisitShape (.sum type arms tag selected)

inductive FlatVisitFocus (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (checkNext : LinkedCallback.FlatSequenceCheckNext grow sig) (canonNext : LinkedCallback.FlatSequenceCanonNext grow sig)
    (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) : Prop where
  | returned (words : List FlatValue) (frame : LinkedCallback.ChildFrameOver older left right check canon)
      (growth : Core3.Grows origin.core left.store.core) (checked : left.ctl = check.control (checkNext (.ok words)))
      (canonical : right.ctl = canon.control (canonNext words)) : FlatVisitFocus older origin checkNext canonNext left right check canon
  | refused (issue : Stored.Endpoints.RecordLower.Issue) (checked : left.ctl = check.control (checkNext (.error issue))) :
      FlatVisitFocus older origin checkNext canonNext left right check canon

abbrev FlatVisitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (checkNext : LinkedCallback.FlatSequenceCheckNext grow sig) (canonNext : LinkedCallback.FlatSequenceCanonNext grow sig) :=
  StringRunSlice profile ready base bindings older (fun _ => FlatVisitFocus older origin checkNext canonNext)

def FlatVisitField (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId) (budget : Nat) (item : Stored.Endpoints.RecordLower.Field) : Prop :=
  open PayloadPrefix Stored.Endpoints.RecordLower in
  ∀ index (checkNext : LinkedCallback.FlatSequenceCheckNext grow sig) (canonNext : LinkedCallback.FlatSequenceCanonNext grow sig)
      left right check canon,
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    left.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index .flat >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item .flat >>= canonNext) →
    ∀ actual finish, Steps profile ready (specDispatch ready base) left actual finish → actual.length ≤ budget →
      FlatVisitRun profile ready base bindings older origin checkNext canonNext left right actual finish

/-- Keep the reached canonical program on a checked-only refusal, either
before the linked field or after the pop at an allocated collection tail. -/
inductive PendingMemoryField (destination : RecordDestination) (inst : InstId)
    (right : Config (core3 grow) (HostState sig)) : Prop where
  | field (peer : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (item : Stored.Endpoints.RecordLower.Field)
      (address : Nat) (next : LinkedCallback.MemorySequence.CanonNext grow sig)
      (atField : right.ctl = peer.control (Stored.Endpoints.RecordLower.CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width item (.memory address) >>= next))
  | collection (peer : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (entries : List Stored.Endpoints.RecordLower.Field)
      (area : ABI.Layout) (pointer address : Nat) (mode : Stored.Endpoints.RecordLower.CanonicalTree.EntryMode)
      (next : LinkedCallback.MemorySequence.CanonNext grow sig)
      (atTail : right.ctl = peer.control (PayloadPrefix.canonicalCollectionTail destination inst entries area (.memory address) pointer mode >>= next))

/-- A visitor can advance a sibling only after a common return. In a paused
allocator keep its current occurrence, even when that occurrence is lost. -/
inductive ValueVisitEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (valueType : Type) (pending : Config (core3 grow) (HostState sig) → Prop)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue valueType → Session grow sig (Ret (core3 grow)))
    (canonNext : valueType → Session grow sig (Ret (core3 grow)))
    (left right : Config (core3 grow) (HostState sig)) (trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) :
    List (Option ReturnFrame.Occurrence.Location) → Prop where
  | returned (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) {value : valueType}
      (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
      (checked : left.ctl = check.control (checkNext (.ok value))) (canonical : right.ctl = canon.control (canonNext value)) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish []
  | refused (issue : Stored.Endpoints.RecordLower.Issue) (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
      (checked : left.ctl = check.control (checkNext (.error issue))) (atPending : pending right) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish []
  | boundary {marks} (reached : StringSliceEnd profile ready base bindings older (fun _ _ _ _ _ => False)
      left right trailing finish marks) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish marks
  | collectionInstall (short : trailing.length < 3) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish []
  | collectionRange {target remaining} (nonempty : remaining ≠ [])
      (tail : Steps profile ready (specDispatch ready base) finish remaining target) :
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish
        [some (.active 0 0)]

/-- An actual checked derivation cut at a compiled visitor endpoint, with a
canonical path to its reached peer and all-location occurrence transport. -/
def ValueVisitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (valueType : Type) (pending : Config (core3 grow) (HostState sig) → Prop)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue valueType → Session grow sig (Ret (core3 grow)))
    (canonNext : valueType → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
    PayloadPrefix.visible checked = PayloadPrefix.visible canonical ∧ left.store = right.store ∧
    OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish marks

abbrev MemoryVisitEnd (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) :=
  ValueVisitEnd profile ready base bindings older origin Unit (PendingMemoryField destination inst) checkNext canonNext

abbrev MemoryVisitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId)
    (checkNext : LinkedCallback.MemorySequence.CheckNext grow sig) (canonNext : LinkedCallback.MemorySequence.CanonNext grow sig) :=
  ValueVisitRun profile ready base bindings older origin Unit (PendingMemoryField destination inst) checkNext canonNext

/-- A local comparison invoked on a real residual from a placed compiled
field. The budget refers to checked steps, not allocator or scheduler fuel. -/
def MemoryVisitField (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId) (budget : Nat)
    (item : Stored.Endpoints.RecordLower.Field) (address : Nat) : Prop :=
  open PayloadPrefix Stored.Endpoints.RecordLower LinkedCallback.MemorySequence in
  ∀ index (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) left right check canon,
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    left.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index (.memory address) >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item (.memory address) >>= canonNext) →
    ∀ actual finish, Steps profile ready (specDispatch ready base) left actual finish → actual.length ≤ budget →
    MemoryVisitRun profile ready base bindings older origin destination inst checkNext canonNext left right actual finish

/-- Comparison of the actual remaining direct field program, including
its original completion continuation. This does not assert the program
pop or that a finite residual reaches the completion. -/
def DirectGiveVisitRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (request : GiveSelector bindings) (ticket : Nat)
    (left right : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  match request.schema with
  | none => MemoryVisitRun profile ready base bindings older left.store request.destination request.inst
      (fun verdict => do return .flat (← writeCompletion (completion ticket (verdict.mapError Issue.lowerPayload |>.map (fun _ => 0)))))
      (fun _ => pure (.flat (completion 0 (.ok 0)).2)) left right actual finish
  | some schema => FlatVisitRun profile ready base bindings older left.store
      (fun verdict => do return .flat (← writeCompletion (flatCompletion ticket (ABI.flatten request.destination.width schema)
        (verdict.mapError Issue.lowerPayload))))
      (fun words => pure (.flat (flatCompletion 0 (ABI.flatten request.destination.width schema) (.ok words)).2))
      left right actual finish

/-- The executed checked-only reply leaves the exact canonical program
pending. Occurrences on the two sides now follow independent paths. -/
def MemoryVisitRefusedReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (incoming left right : Config (core3 grow) (HostState sig)) (issue : Stored.Endpoints.RecordLower.Issue)
    (checkLeading canonLeading actual trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  trailing.length < 3 ∨
    CheckedOnlyGiveReply profile ready base bindings (.memory pointer) site.destination site.start.host.nextTicket issue
      site.start incoming left right checkLeading canonLeading trailing finish ∧
    ∀ {label next}, GiveInstall bindings (specDispatch ready base) site.start label next →
      CallbackSlice profile ready base bindings older site.start incoming actual finish

/-- A common reply carries the complete request and its original occurrence
paths. A reached uncertified growth step is explicit, not silently replayed. -/
def GiveVisitCommonReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {route : GiveEffectRoute}
    (site : PayloadRoot.Site grow sig route) (value : route.output.Result) (incoming left right : Config (core3 grow) (HostState sig))
    (checkEntry checkBody canonLeading actual trailing : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  trailing.length < 3 ∨ ∃ suffix checked canonical,
    trailing = [.tau, .tau, .tau] ++ suffix ∧ suffix.length < actual.length ∧
    Steps profile ready (specDispatch ready base) checked suffix finish ∧
    checked.host = left.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1 ∧
    canonical.host = right.host ∧
    let checkFull := (checkEntry ++ checkBody) ++ [.tau, .tau, .tau]
    let canonFull := canonLeading ++ [.tau]
    (ExecutedCallbackSegment profile ready base bindings older site.start incoming checkFull canonFull checked canonical ∧
      CallbackSlice profile ready base bindings older site.start incoming (checkEntry ++ actual) finish) ∨
      (ReachedNonGrowingUpdate profile ready (specDispatch ready base) site.start checkFull checked ∧
        HostFrame.Related.Paired older checked canonical ∧
        OccurrenceTransport profile ready base bindings site.start incoming checkFull canonFull checked canonical)

abbrev MemoryVisitCommonReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) :=
  GiveVisitCommonReply profile ready base bindings older site ()

/-- The reached visit retains both traces and the move used by all older
occurrences. A reply requires the original call occurrence at the top. -/
def MemoryVisitWithReply (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming entered : Config (core3 grow) (HostState sig))
    (checkEntry canonEntry actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checked canonical trailing left right marks, ∃ (move : Option Location → Option Location),
    actual = checked ++ trailing ∧ PayloadPrefix.visible checked = PayloadPrefix.visible canonical ∧ left.store = right.store ∧
    (∀ cursor, Trail profile ready (specDispatch ready base) site.checked cursor checked left (move cursor) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) entered cursor canonical right (move cursor)) ∧
    (∀ changes retained, OutsideMarks changes (segmentStorage site.checked) (segmentStorage entered) retained →
      OutsideMarks changes (segmentStorage left) (segmentStorage right) (marks ++ retained.map move)) ∧
    Steps profile ready (specDispatch ready base) left trailing finish ∧
    MemoryVisitEnd profile ready base bindings older site.checked.store site.destination site.inst
      site.reply site.referenceReply left right trailing finish marks ∧
    (move (some (.active 0 0)) = some (.active 0 0) →
      (marks = [] → (∃ (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)),
          LinkedCallback.ChildFrameOver older left right check canon ∧
          left.ctl = check.control (site.reply (.ok ())) ∧ right.ctl = canon.control (site.referenceReply ())) →
        MemoryVisitCommonReply profile ready base bindings older site incoming left right
          checkEntry checked (canonEntry ++ canonical) actual trailing finish) ∧
      ∀ issue (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)), left.ctl = check.control (site.reply (.error issue)) →
        MemoryVisitRefusedReply profile ready base bindings older site incoming left right issue
          (checkEntry ++ checked) (canonEntry ++ canonical) (checkEntry ++ actual) trailing finish) ∧
    ∀ {label next}, GiveInstall bindings (specDispatch ready base) site.start label next →
      CallbackSlice profile ready base bindings older site.start incoming (checkEntry ++ actual) finish

/-- On the placed branch, distinguish a finite prefix inside entry from
an actually reached body. No canonical body path is used in the short case. -/
def ActualMemoryRequestRun (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) {pointer : FlatValue}
    (site : PayloadRoot.Site grow sig (.memory pointer)) (incoming : Config (core3 grow) (HostState sig))
    (actual : Trace grow sig) (finish : Config (core3 grow) (HostState sig)) : Prop :=
  open ReturnFrame.Occurrence in
  ∃ checkEntry, site.EntryPrefix profile ready base checkEntry site.checked ∧ PayloadPrefix.visible checkEntry = [] ∧
    ((∃ remaining, checkEntry = actual ++ remaining ∧ remaining ≠ [] ∧
      Steps profile ready (specDispatch ready base) finish remaining site.checked) ∨
    ∃ canonEntry entered body, actual = checkEntry ++ body ∧ PayloadPrefix.visible canonEntry = [] ∧
      (∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
        incoming place canonEntry entered (site.entryPlace place)) ∧ entered.host = incoming.host ∧
      MemoryVisitWithReply profile ready base bindings older site incoming entered checkEntry canonEntry body finish) ∧
    ∀ {label next}, GiveInstall bindings (specDispatch ready base) site.start label next →
      CallbackSlice profile ready base bindings older site.start incoming actual finish

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
