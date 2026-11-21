module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Dispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Traversal.Defs

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
not install an overlaid give or assign the host; confined gives and the
actual synchronous readiness read have their own rules. The endpoint may
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
  | syncReady {start finish seen task inst thread frames rest}
      (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun current =>
        syncLiftCandidates task (start.store.instCandidates (ready current) inst))), frames⟩ :: rest)
      (agrees : LinkedCallback.ReadyAgreement ready start inst)
      (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn { start with ctl := ⟨thread,
        .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) inst)), frames⟩ :: rest } seen finish) :
      ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish

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

def stringAllocatorEntry (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat) (alignment : ABI.Alignment) (size : Nat)
    (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) : Config (core3 grow) (HostState sig) :=
  let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
  { state with ctl := { cursor with frames := .prog resume :: cursor.frames }.control (dispatch request) }

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
    CoupledOccurrencePaths profile ready base bindings left right labels labels lhs rhs ∧
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
        ∀ {seen reached}, ClosedCallbackPrefix bindings profile ready base
          (fun resume => (∃ peer, older resume peer) ∨ resume = first) firstEntry seen reached →
          ∃ checkLabels canonLabels reference mark,
            Steps profile ready checkDispatch lhs (.tau :: checkLabels) reached ∧
            Steps profile ready canonDispatch rhs (.tau :: canonLabels) reference ∧
            visible checkLabels = seen ∧ visible canonLabels = seen ∧
            HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
            Core3.Grows lhs.store.core reached.store.core ∧
            reached.host.writer.accepted = lhs.host.writer.accepted ∧
            reference.host.writer.accepted = rhs.host.writer.accepted ∧
            AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
            CoupledOccurrencePaths profile ready base bindings lhs rhs (.tau :: checkLabels) (.tau :: canonLabels) reached reference ∧
            ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
              reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
              ∃ peer : Cursor (E := core3 grow) (HostState sig),
                let after := { reached with ctl := cursor.control (first (.nat value)) }
                let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
                RetainsActiveSlots profile ready checkDispatch lhs (.tau :: checkLabels ++ [.tau]) after ∧
                RetainsActiveSlots profile ready canonDispatch rhs (.tau :: canonLabels ++ [.tau]) referenceAfter ∧
                CoupledOccurrencePaths profile ready base bindings lhs rhs (.tau :: checkLabels ++ [.tau])
                  (.tau :: canonLabels ++ [.tau]) after referenceAfter ∧
                LiveStringReplay profile ready base bindings older cx checkNext canonNext finish rest.length after referenceAfter cursor peer
termination_by length

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

/-- Cumulative all-location trails through the actual string plan. A finite
callback path need not reach a pop. Only the installed frame's actual return
continues the decreasing residual plan. -/
def LiveStringOccurrences (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (cx : LiftLowerContext (core3 grow))
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (leftStart rightStart : Config (core3 grow) (HostState sig))
    (finish : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop)
    (length : Nat) (left right : Config (core3 grow) (HostState sig))
    (check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (seen : Trace grow sig) : Prop :=
  open PayloadPrefix ReturnFrame.Occurrence in
  ∃ (store : CStore (core3 grow)) (result : Except TrapReason (StringFront length)) (labels : Trace grow sig),
    let lhs := localLeafEnd left left.host store check.thread check.frames check.rest
      (fun front : StringFront length => front.remaining cx >>= checkNext) result
    let rhs := localLeafEnd right right.host store canon.thread canon.frames canon.rest
      (fun front : StringFront length => front.remaining cx >>= canonNext) result
    LocalLeafLabels result labels ∧
    ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ visible labels) lhs rhs ∧
    match result with
    | .error _ => lhs.ctl = [] ∧ rhs.ctl = []
    | .ok (.done pointer) => finish pointer lhs rhs check canon
    | .ok (.call pointer oldSize alignment size rest _) =>
      let first := stringPlanResume cx rest checkNext
      let second := stringPlanResume cx rest canonNext
      let firstEntry := LinkedCallback.stringReallocEntry ready bindings cx pointer oldSize alignment size rest checkNext lhs check
      let secondEntry := stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base))
        cx pointer oldSize alignment size rhs canon second
      ∀ {observed reached}, ClosedCallbackPrefix bindings profile ready base
        (fun resume => (∃ peer, older resume peer) ∨ resume = first) firstEntry observed reached →
        ∃ checkLabels canonLabels reference mark,
          AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
          HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
          ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ observed) reached reference ∧
          ∀ (value : Nat) (cursor : Cursor (E := core3 grow) (HostState sig)), mark = some (.active 0 0) →
            reached.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat value)) →
            ∃ peer : Cursor (E := core3 grow) (HostState sig),
              let after := { reached with ctl := cursor.control (first (.nat value)) }
              let referenceAfter := { reference with ctl := peer.control (second (.nat value)) }
              ComparedOccurrencePaths profile ready base bindings leftStart rightStart (seen ++ observed) after referenceAfter ∧
              LiveStringOccurrences profile ready base bindings older cx checkNext canonNext leftStart rightStart finish
                rest.length after referenceAfter cursor peer (seen ++ observed)
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
def DerivesFlatFieldTrail (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (destination : RecordDestination) (inst : InstId) (sink : RefusalSink grow sig)
    (path : FlatFieldTrail grow sig) (item : Stored.Endpoints.RecordLower.Field) : Prop :=
  open Stored.Endpoints.RecordLower in
  ∀ index checkNext canonNext finish before left right check canon,
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    ComparedSlots profile ready base bindings start incoming before left right offset →
    sink.admits (fun issue => checkNext (.error issue)) →
    left.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index .flat >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item .flat >>= canonNext) →
    (∀ words seen lhs rhs cursor peer, LinkedCallback.ChildFrameOver older lhs rhs cursor peer →
      Core3.Grows origin.core lhs.store.core → ComparedSlots profile ready base bindings start incoming seen lhs rhs offset →
      lhs.ctl = cursor.control (checkNext (.ok words)) → rhs.ctl = peer.control (canonNext words) →
      finish words seen lhs rhs cursor peer) →
    path item index checkNext canonNext finish before left right check canon

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

/-- The local induction interface for a compiled field. Only the field's
actual success continuation advances a sibling; other branches are handled
by that field's reached path comparison. -/
def LiftsFieldPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (field : LinkedCallback.MemorySequence.FieldComparison grow sig) (paths : TrailFieldComparison grow sig)
    (sink : RefusalSink grow sig := .ignore) : Prop :=
  ∀ item index address left right check canon checkNext canonNext finish visit before,
    field item index address left right check canon checkNext canonNext finish →
    ComparedSlots profile ready base bindings start incoming before left right offset →
    left.store = right.store →
    sink.admits (fun issue => checkNext (.error issue)) →
    (∀ seen lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming seen lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit seen lhs rhs cursor peer) →
    paths item index address checkNext canonNext visit before left right check canon

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
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base))
      right mode.readLabels reference ∧
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
      ∀ {observed reached}, ClosedCallbackPrefix bindings profile ready base
        (fun resume => (∃ peer, older resume peer) ∨ resume = first) firstEntry observed reached →
        ∃ checkLabels canonLabels reference mark,
          AllocatorMark profile ready base bindings older firstEntry secondEntry checkLabels canonLabels reached reference mark ∧
          HostFrame.Related.Paired (ReturnFrame.Extend older first second) reached reference ∧
          ComparedAllocatorPaths profile ready base bindings leftStart rightStart (seen ++ observed) reached reference offset ∧
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

/-- Entry into the exact recursive bodies of a nested collection after its
marked allocator returns, range checks pass and a fresh reservation succeeds.
The frame and cumulative trails are for the reached state, not the state
before the allocator. Memory-map placement keeps its allocation-time mode. -/
def LiveCollectionChildren (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Stored.Endpoints.RecordLower.Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (start incoming : Config (core3 grow) (HostState sig)) (pointer bytes : Nat)
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (observed : Trace grow sig)
    (visit : LinkedCallback.MemorySequence.Finish grow sig := fun _ _ _ _ => True)
    (leftStart : Config (core3 grow) (HostState sig) := start)
    (rightStart : Config (core3 grow) (HostState sig) := incoming) (offset : Nat := 0) : Prop :=
  open Stored.Endpoints.RecordLower ABI PayloadPrefix in
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  ∃ left right canon,
    ComparedSlots profile ready base bindings leftStart rightStart observed left right offset ∧
    LinkedCallback.ChildFrameOver older left right check canon ∧
    (core3 grow).memAddrType? left.store.core destination.memory = some destination.width ∧
    (core3 grow).memSize? left.store.core destination.memory = some bytes ∧
    pointer = alignTo pointer area.alignment ∧ pointer + entries.length * area.size ≤ bytes ∧
    Core3.Grows start.store.core left.store.core ∧
    left.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) ∧
    right.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) ∧
    visit left right check canon

/-- The unsuccessful branches of a marked range return, measured from the
same origin as the recursive body. Range traps run on both sides. A fresh
reservation failure follows only the checked issue continuation; the
canonical cursor is at its unexecuted child program. -/
def CollectionRangePaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (leftStart rightStart : Config (core3 grow) (HostState sig)) (observed : Trace grow sig) (offset : Nat)
    (destination : RecordDestination) (area : ABI.Layout) (entries : List Stored.Endpoints.RecordLower.Field)
    (pointer : Nat) (checked canonical : Config (core3 grow) (HostState sig))
    (check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (refuse : IssueProgram grow sig) (wrap : Stored.Endpoints.RecordLower.Issue → Stored.Endpoints.RecordLower.Issue)
    (children : Session grow sig (Ret (core3 grow))) (sink : RefusalSink grow sig := .ignore) : Prop :=
  open Stored.Endpoints.RecordLower in
  let trap := fun reason => ComparedPaths profile ready base bindings leftStart rightStart (observed ++ [.trap reason])
    (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical)
  ∃ bytes, (core3 grow).memSize? checked.store.core destination.memory = some bytes ∧
    if pointer ≠ ABI.alignTo pointer area.alignment then trap .unalignedPointer
    else if pointer + entries.length * area.size ≤ bytes then
      ∀ issue, OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
        ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
          let stopped := { checked with ctl := check.control (refuse (wrap issue)) }
          let reference := { canonical with ctl := canon.control children }
          checked.store = canonical.store ∧ ComparedSlots profile ready base bindings leftStart rightStart observed
            stopped reference offset ∧ sink.exit refuse (wrap issue) observed stopped reference check
    else trap .outOfBounds

/-- Finite callback paths for an actual dynamic child. A live mark at the
natural-pointer return is required to inspect the range. Failed range checks
trap, and a failed fresh reservation does not enter the children. -/
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
  ∀ {seen finish}, ClosedCallbackPrefix bindings profile ready base
      (fun resume => (∃ peer, older resume peer) ∨ resume = first) leftEntry seen finish →
    ∃ checkLabels canonLabels reached mark,
      AllocatorMark profile ready base bindings older leftEntry rightEntry checkLabels canonLabels finish reached mark ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      ComparedAllocatorPaths profile ready base bindings leftStart rightStart (leading ++ seen) finish reached offset ∧
      ∀ pointer cursor, mark = some (.active 0 0) →
        finish.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
        CollectionRangeCut profile ready base bindings older finish reached cursor destination area entries.length pointer
          (Stored.Endpoints.RecordLower.Field.listObjects entries)
          (fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
          (fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) ∧
        CollectionRangePaths profile ready base bindings leftStart rightStart (leading ++ seen) offset destination area entries
          pointer finish reached cursor (fun issue => checkNext (.error issue)) (LinkedCallback.CollectionVisit.afterAllocation index)
          (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) sink ∧
        ∀ bytes, (core3 grow).memSize? finish.store.core destination.memory = some bytes →
          pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
          OwnedMemory.Claims.Record.prepare finish.store finish.host.writer (Field.listObjects entries) = .ok () →
          LiveCollectionChildren profile ready base bindings older destination inst type element entries index output checkNext
            canonNext start incoming pointer bytes cursor (leading ++ seen) (visit pointer bytes (leading ++ seen)) leftStart rightStart offset

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
    ∃ keyRead, visible keyRead = [] ∧ RetainsActiveSlots profile ready canonical right keyRead atKey ∧
    ∃ (store : CStore (core3 grow)) (result : Except TrapReason Unit) (checkLabels canonLabels : Trace grow sig),
      let lhs := localLeafEnd left left.host store check.thread check.frames check.rest valCheck result
      let rhs := localLeafEnd atKey right.host store canon.thread canon.frames canon.rest valCanon result
      Steps profile ready checked left checkLabels lhs ∧ LocalSteps profile ready canonical atKey canonLabels rhs ∧
      visible checkLabels = visible canonLabels ∧
      match result with
      | .error reason => ∃ leading, visible canonLabels = leading ++ [.trap reason]
      | .ok () =>
        let atValue := { rhs with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none cx destination.width value
          (.memory valPtr) >>= canonNext) }
        RetainsActiveSlots profile ready checked left checkLabels lhs ∧
        RetainsActiveSlots profile ready canonical atKey canonLabels rhs ∧
        ∃ valueRead, visible valueRead = [] ∧ RetainsActiveSlots profile ready canonical rhs valueRead atValue ∧
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
    ComparedSlots profile ready base bindings start incoming seen refused right offset ∧ refused.store = right.store ∧
      sink.exit (fun reason => checkNext (.error reason)) issue seen refused right check) ∨
  LocalPathsThen profile ready base bindings start incoming seen offset finish

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
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready base) left checkLabels checkBody ∧
    ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base))
      right canonLabels canonBody ∧
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
def flatSumPaths (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (offset : Nat)
    (width : AddrType) (type : Stored.TypeOf) (arms : List (Option Stored.TypeOf))
    (pick : Nat → FlatFieldTrail grow sig) : FlatFieldTrail grow sig :=
  fun item index checkNext canonNext finish before left right check canon =>
    open LinkedCallback ABI in
    ∃ tag selected, item = .sum type arms tag selected ∧
      match selected with
      | none => LocalPathsThen profile ready base bindings start incoming before offset (flatWordVisit finish)
      | some child =>
        let haves := flatten width child.type
        pick tag child 0 (flatSumCheckNext width type arms.length tag index haves checkNext)
          (fun words => flatSumTail width type arms.length tag haves words >>= canonNext)
          (fun _ observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset (flatWordVisit finish))
          before left right check canon

abbrev TrailLeafType (type : Stored.TypeOf) : Prop :=
  NominalElement type ∨ PayloadPrefix.LocalDataType type ∨ type = .prim .string

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
        checkNext canonNext (fun _ observed _ _ _ _ => LocalPathsThen profile ready base bindings start incoming observed offset finish)
        before offset
  | .prim _ | .enum _ | .flags _ => fun _ _ _ _ _ finish before _ _ _ _ =>
    LocalPathsThen profile ready base bindings start incoming before offset finish
  | _ => fun item index _ checkNext _ finish before left right check _ =>
    HandlePathsThen profile ready base bindings start incoming before offset item index checkNext finish left right check sink

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
        (fun result => checkNext (.ok result)) canonNext)

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
            match result with
            | .error _ => True
            | .ok () =>
              RetainsActiveSlots profile ready checkDispatch lhs labels checkEnd ∧
              RetainsActiveSlots profile ready canonDispatch rhs labels canonEnd ∧
              let atValue := { canonEnd with ctl := peer.control (CanonicalTree.field Limits.spec Quirks.none cx
                destination.width value (.memory valuePtr) >>= canonNext) }
              ∃ widthRead, visible widthRead = [] ∧ RetainsActiveSlots profile ready canonDispatch canonEnd widthRead atValue ∧
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

/-- Select the reached map key program before the recursive value. The
canonical entry mode is fixed by the allocation's output, not the value. -/
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
    RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base)) right [.tau] reference ∧
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
  RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base)) right [.tau] reference ∧
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
  RetainsActiveSlots profile ready (specDispatch ready base) left [.tau] entered ∧
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
    RetainsActiveSlots profile ready (specDispatch ready base) left [.tau] entered ∧
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
  | .option element => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.option element) [none, some element] tag selected ∧
      LocalPathsThen profile ready base bindings start incoming before offset
        (match selected with
        | none => finish
        | some arm => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink element arm 0
            (PayloadPrefix.sumPayloadAddress destination.width [none, some element] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .result success failure => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      let okPaths : TrailFieldComparison grow sig := match success with
        | some type => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      let errorPaths : TrailFieldComparison grow sig := match failure with
        | some type => liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type
        | none => fun _ _ _ _ _ _ _ _ _ _ _ => False
      LocalPathsThen profile ready base bindings start incoming before offset
        (match selected with
        | none => finish
        | some arm => (if tag = 0 then okPaths else errorPaths) arm 0 (PayloadPrefix.sumPayloadAddress destination.width [success, failure] address)
            (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish)
  | .variant cases => fun item index address checkNext canonNext finish before _ _ _ _ =>
    ∃ tag selected, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      LocalPathsThen profile ready base bindings start incoming before offset
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
  | _ => fun _ _ _ _ finish before _ _ _ _ =>
    LocalPathsThen profile ready base bindings start incoming before offset (flatWordVisit finish)
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
  | compiled {tag payload arity children field plan} (preflight : selection.preflight = .ok (field, plan))
      (root : selection.tree = .tag ⟨tag, payload⟩ arity children)
      (linked : (selection.site tag payload arity children field).Linked bindings)
      (cut : ReachedRecursiveRoot profile ready bindings callees older incoming (selection.site tag payload arity children field))

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
      (left : Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (List.replicate leftCount .tau) checked)
      (right : Steps profile ready (specDispatch ready (host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming (List.replicate rightCount .tau) canonical)
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

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
