module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FlatTrails
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCollection.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.CollectionVisit.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Component.Reference.ABI.Layout.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
open ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}

theorem collectionRange (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {start canonStart checked canonical : Config (core3 grow) (HostState sig)}
    {checkEntry canonEntry cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start checkEntry first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        canonStart canonEntry second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
    (core3 grow).memAddrType? start.store.core destination.memory = some destination.width →
    Core3.Grows start.store.core checked.store.core →
    CollectionRangeCut profile ready base bindings older checked canonical cursor destination area entries.length pointer
      (Field.listObjects entries)
      (fun addr verdict => PayloadPrefix.checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
      (fun addr => PayloadPrefix.canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) := by
  intro area mode first second marked paired returning present growth
  obtain ⟨place, origin, trail⟩ := marked.canonicalTrail.survives
  cases origin
  have canonicalTop : segmentAt (segmentStorage canonical) (.active 0 0) = some (.prog second) :=
    (prefix_survives trail).2.trans rfl
  obtain ⟨canonCursor, frame, canonicalAt⟩ := LinkedCallback.marked_pop_frame paired marked.outside returning canonicalTop
  have width : (core3 grow).memAddrType? checked.store.core destination.memory = some destination.width := growth.memAddrType present
  have hasSize : ((core3 grow).memSize? checked.store.core destination.memory).isSome := by
    apply Core3.memAddrType?_isSome_iff.mp
    change ((core3 grow).memAddrType? checked.store.core destination.memory).isSome = true
    rw [width]
    rfl
  obtain ⟨bytes, sized⟩ := Option.isSome_iff_exists.mp hasSize
  have returned : canonical.ctl = ⟨cursor.thread, .prog (.pure (.nat pointer)),
      .prog second :: canonCursor.frames⟩ :: canonCursor.rest := by
    simpa only [PayloadPrefix.Cursor.control, ← frame.thread] using canonicalAt
  refine ⟨canonCursor, bytes, width, sized, frame, ?_⟩
  have validated := destination.paired_range_recheck (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    paired inst area entries.length pointer (Field.listObjects entries)
    (fun addr verdict => PayloadPrefix.checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
    (fun addr => PayloadPrefix.canonicalCollectionTail destination inst entries area output addr mode >>= canonNext)
    rfl rfl returning returned sized (specDispatch ready (LiveDispatch.host bindings base))
  simpa only [PayloadPrefix.Cursor.control, ← frame.thread] using validated

private theorem silent {labels : Trace grow sig} (tau : ∀ label ∈ labels, label = .tau) : visible labels = [] := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    have head := tau label (by simp)
    have tail := ih (fun other member => tau other (List.mem_cons_of_mem _ member))
    subst label
    exact tail

private theorem appendRun {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start middle finish : Config (core3 grow) (HostState sig)} {leading trailing}
    (front : Steps profile ready dispatch start leading middle) (back : Steps profile ready dispatch middle trailing finish) :
    Steps profile ready dispatch start (leading ++ trailing) finish := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

private theorem appendVisible (first second : Trace grow sig) :
    visible (first ++ second) = visible first ++ visible second := List.filter_append ..

private theorem initialSlots (left right : Config (core3 grow) (HostState sig)) :
    ComparedSlots profile ready base bindings left right [] left right :=
  ⟨[], [], fun _ => .done _ _, fun _ => .done _ _, rfl, rfl⟩

private def CollectionVisitor (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (visit : Nat → Nat → Finish grow sig) : Prop :=
  let area := layout destination.width element
  let mode := CanonicalTree.EntryMode.forOutput destination.width type output
  ∀ pointer bytes lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
    Core3.Grows origin.core lhs.store.core →
    (core3 grow).memAddrType? lhs.store.core destination.memory = some destination.width →
    (core3 grow).memSize? lhs.store.core destination.memory = some bytes →
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    lhs.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) →
    rhs.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) →
    visit pointer bytes lhs rhs check canon

private theorem collectionPathsFrom (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {start incoming : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (prepared : Record.prepare start.store start.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (visit : Nat → Nat → Finish grow sig)
    (children : CollectionVisitor destination inst type element entries index output checkNext canonNext older start.store visit)
    {leftStart rightStart : Config (core3 grow) (HostState sig)} {before : Trace grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart before start incoming offset) :
    LiveCollectionPaths profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon (fun pointer bytes _ => visit pointer bytes) leftStart rightStart before offset := by
  unfold LiveCollectionPaths
  intro area mode first second leftEntry rightEntry seen finish path
  obtain ⟨lhs, rhs, reached, mark, checkRun, canonRun, paired, checkSeen, canonSeen, growth, _, _, marked⟩ :=
    CallbackPrefix.collectionPrefix (profile := profile) (ready := ready) destination inst type element entries output index
      checkNext canonNext frame width prepared checkAt canonAt embedder path
  have checkObserved : visible ([.tau, .tau, .tau] ++ lhs) = seen := by
    rw [appendVisible, silent (by simp), List.nil_append, checkSeen]
  have canonObserved : visible ([.tau, .tau] ++ rhs) = seen := by
    rw [appendVisible, silent (by simp), List.nil_append, canonSeen]
  have sameStore : finish.store = reached.store := by
    change ReturnFrame.Related.Paired _ (HostFrame.replace finish reached.host) reached at paired
    generalize reached.host = observer at paired
    cases paired
    rfl
  have leftInstall := fun depth => (PayloadPrefix.collection_install_tracks (profile := profile) (ready := ready)
    (dispatch := specDispatch ready base) destination inst type element entries output index start incoming check canon
    checkNext canonNext width prepared checkAt canonAt depth).1
  have rightInstall := fun depth => (PayloadPrefix.collection_install_tracks (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) destination inst type element entries output index
    start incoming check canon checkNext canonNext width prepared checkAt canonAt depth).2
  refine ⟨lhs, rhs, reached, mark, marked, paired, CallbackPrefix.appendAllocatorPaths leading
    (CallbackPrefix.allocatorPaths leftInstall rightInstall marked checkObserved canonObserved sameStore), ?_⟩
  intro pointer cursor atTop returning
  subst mark
  have cut := collectionRange (profile := profile) (ready := ready) destination inst type element entries output index pointer
    checkNext canonNext marked paired returning (frame.store ▸ width) growth
  have ⟨peer, capacity, liveWidth, liveSize, frameAtReturn, outcomes⟩ := cut
  have slotsAfter {left right : Config (core3 grow) (HostState sig)} {checkTail canonTail : Trace grow sig}
      (checkTau : ∀ label ∈ checkTail, label = .tau) (canonTau : ∀ label ∈ canonTail, label = .tau)
      (checkTracks : RetainsBelowTop profile ready (specDispatch ready base) finish checkTail left)
      (canonTracks : RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base)) reached canonTail right) :
      ComparedSlots profile ready base bindings leftStart rightStart (before ++ seen) left right offset := by
    refine CallbackPrefix.appendComparedSlots leading
      ⟨[.tau, .tau, .tau] ++ (lhs ++ checkTail), [.tau, .tau] ++ (rhs ++ canonTail),
      marked.checkedTrail.through_return_suffix leftInstall checkTracks, marked.canonicalTrail.through_return_suffix rightInstall canonTracks,
      ?_, ?_⟩
    · rw [← List.append_assoc, appendVisible, checkObserved, silent checkTau, List.append_nil]
    · rw [← List.append_assoc, appendVisible, canonObserved, silent canonTau, List.append_nil]
  have traps (reason : TrapReason)
      (checkStop : ∃ count, Steps profile ready (specDispatch ready base) finish
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg finish))
      (canonStop : ∃ count, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) reached
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg reached)) :
      ComparedPaths profile ready base bindings leftStart rightStart ((before ++ seen) ++ [.trap reason])
        (StepDefs.trapCfg finish) (StepDefs.trapCfg reached) := by
    obtain ⟨leftCount, checkSteps⟩ := checkStop
    obtain ⟨rightCount, canonSteps⟩ := canonStop
    have seenTrap (count : Nat) : visible (List.replicate count (.tau : Label (core3 grow) (HostState sig)) ++ [.trap reason]) =
        [.trap reason] := by
      rw [appendVisible, silent (fun _ member => List.eq_of_mem_replicate member)]
      rfl
    rw [List.append_assoc]
    exact CallbackPrefix.appendComparedPaths leading ⟨_, _, appendRun checkRun checkSteps, appendRun canonRun canonSteps,
      by rw [appendVisible, checkObserved, seenTrap], by rw [appendVisible, canonObserved, seenTrap],
      congrArg StepDefs.lockdownSt sameStore⟩
  refine ⟨cut, ?_, ?_⟩
  · refine ⟨capacity, liveSize, ?_⟩
    by_cases aligned : pointer = alignTo pointer (layout destination.width element).alignment
    · rw [ite_eq_right (not_not_intro aligned)] at outcomes ⊢
      by_cases bounds : pointer + entries.length * (layout destination.width element).size ≤ capacity
      · rw [ite_eq_left bounds] at outcomes ⊢
        intro issue fresh
        rw [fresh] at outcomes
        obtain ⟨⟨_, checkTau, checkTracks⟩, ⟨_, canonTau, canonTracks⟩⟩ := outcomes
        have stopped : (checkedCollectionTail destination inst entries area index output pointer (.error issue) >>= checkNext) =
            checkNext (.error (LinkedCallback.CollectionVisit.afterAllocation index issue)) := by cases issue <;> rfl
        change RetainsBelowTop profile ready (specDispatch ready base) finish _
          { finish with ctl := cursor.control (checkedCollectionTail destination inst entries area index output pointer
            (.error issue) >>= checkNext) } at checkTracks
        rw [stopped] at checkTracks
        exact ⟨peer, sameStore, slotsAfter checkTau canonTau checkTracks canonTracks, trivial⟩
      · rw [ite_eq_right bounds] at outcomes ⊢
        exact traps .outOfBounds outcomes.1 outcomes.2
    · rw [ite_eq_left aligned] at outcomes ⊢
      exact traps .unalignedPointer outcomes.1 outcomes.2
  intro bytes sized aligned bounds fresh
  have capacityEq := Option.some.inj (liveSize.symm.trans sized)
  rw [ite_eq_right (not_not_intro aligned), capacityEq, ite_eq_left bounds, fresh] at outcomes
  obtain ⟨⟨checkTail, checkTau, checkTracks⟩, ⟨canonTail, canonTau, canonTracks⟩⟩ := outcomes
  have frameAfter : LinkedCallback.ChildFrameOver older
      { finish with ctl := cursor.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext) }
      { reached with ctl := peer.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext) }
      cursor peer :=
    ⟨frameAtReturn.store, frameAtReturn.pending, frameAtReturn.results, frameAtReturn.cancels, frameAtReturn.blocked,
      frameAtReturn.thread, frameAtReturn.frames, frameAtReturn.rest⟩
  exact ⟨_, _, peer, slotsAfter checkTau canonTau checkTracks canonTracks, frameAfter, liveWidth, sized, aligned, bounds,
    growth, rfl, rfl, children pointer bytes _ _ _ _ frameAfter growth liveWidth sized aligned bounds rfl rfl⟩

private theorem collectionEntryVisiting (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {start incoming : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (visit : Nat → Nat → Finish grow sig)
    (children : CollectionVisitor destination inst type element entries index output checkNext canonNext older start.store visit)
    {leftStart rightStart : Config (core3 grow) (HostState sig)} {before : Trace grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart before start incoming offset) :
    LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon (fun pointer bytes _ => visit pointer bytes) leftStart rightStart before offset := by
  unfold LiveCollectionEntry
  cases prepared : Record.prepare start.store start.host.writer (Field.listObjects entries) with
  | ok result =>
    cases result
    exact fun width => collectionPathsFrom destination inst type element entries index output checkNext canonNext
      frame width prepared checkAt canonAt embedder visit children leading
  | error issue =>
    let entered := fun verdict : Except RecordLower.Issue Unit => (match verdict with
      | .error (.preflight issue) => pure (.error (.field index (.beforeAllocation issue)))
      | .error issue => pure (.error (.nested index issue))
      | .ok () => do
        let area := layout destination.width element
        let ptr ← allocateListRange (destination.context inst) area entries.length
        let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
        checkedCollectionTail destination inst entries area index output ptr live) >>= checkNext
    have fetched : start.ctl = check.control (.op .get fun store => .op .hostGet fun host =>
        entered (Record.prepare store host.writer (Field.listObjects entries))) := by
      rw [Record.Effects.field] at checkAt
      exact checkAt
    have track : RetainsActiveSlots profile ready (specDispatch ready base) start [.tau, .tau]
        { start with ctl := check.control (entered (.error issue)) } := by
      intro depth
      refine .step (middle := .active 0 depth) (.get fetched) ?_
        (.step (middle := .active 0 depth) (.hostGet rfl) rfl ?_)
      · rw [ReturnFrame.Occurrence.transitionEdit, fetched]
        rfl
      · rw [prepared]
        exact .done _ _
    have reached := CallbackPrefix.appendComparedSlots leading
      ⟨[.tau, .tau], [], track, fun depth => .done incoming (.active 0 depth), rfl, rfl⟩
    rw [show visible ([.tau, .tau] : Trace grow sig) = [] from rfl, List.append_nil] at reached
    exact ⟨frame.store, canonAt, by cases issue <;> exact reached, trivial⟩

theorem collectionEntryPathsFrom (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {start incoming : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {leftStart rightStart : Config (core3 grow) (HostState sig)} {before : Trace grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart before start incoming offset) :
    LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming check canon (fun _ _ _ _ _ _ _ => True) leftStart rightStart before offset :=
  collectionEntryVisiting destination inst type element entries index output checkNext canonNext frame checkAt canonAt embedder
    (fun _ _ _ _ _ _ => True) (by unfold CollectionVisitor; intros; exact True.intro) leading

private theorem leafSilent {Result : Type} {value : Result} {labels : Trace grow sig}
    (quiet : LocalLeafLabels (.ok value) labels) : visible labels = [] := by
  apply silent
  intro label member
  have tau := List.all_eq_true.mp quiet label member
  cases label <;> simp_all

private theorem leafTrap {Result : Type} {reason : TrapReason} {labels : Trace grow sig}
    (traps : LocalLeafLabels (Result := Result) (.error reason) labels) : visible labels = [.trap reason] := by
  obtain ⟨count, rfl⟩ := traps
  rw [appendVisible, silent (fun _ member => List.eq_of_mem_replicate member)]
  rfl

private theorem prependSegment {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {startLeft startRight left right : Config (core3 grow) (HostState sig)} {leftLabels rightLabels : Trace grow sig}
    {cursor : Cursor (E := core3 grow) (HostState sig)} {Result : Type}
    {checkNext : Except RecordLower.Issue Result → Session grow sig (Ret (core3 grow))}
    {canonNext : Result → Session grow sig (Ret (core3 grow))}
    {stopsAt : Session grow sig (Ret (core3 grow)) → Prop} {keep : CStore (core3 grow) → Prop} {offset : Nat}
    (leftTracks : ∀ depth, Prefix profile ready (specDispatch ready base) startLeft (.active 0 (depth + offset)) leftLabels left (.active 0 depth))
    (rightTracks : ∀ depth, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      startRight (.active 0 (depth + offset)) rightLabels right (.active 0 depth))
    (seen : visible leftLabels = visible rightLabels)
    (tail : CollectionSegment profile ready base bindings older left right cursor checkNext canonNext 0 stopsAt keep) :
    CollectionSegment profile ready base bindings older startLeft startRight cursor checkNext canonNext offset stopsAt keep := by
  obtain ⟨peer, outcome, checkLabels, canonLabels, lhs, rhs, checkRun, canonRun, same, observations, status⟩ := tail
  refine ⟨peer, outcome, _, _, lhs, rhs, appendRun (prefix_survives (leftTracks 0)).1 checkRun,
    appendRun (prefix_survives (rightTracks 0)).1 canonRun, same, by rw [appendVisible, appendVisible, seen, observations], ?_⟩
  cases outcome with
  | trapped reason =>
    obtain ⟨leftTrap, rightTrap, leading, canonTrap⟩ := status
    exact ⟨leftTrap, rightTrap, visible rightLabels ++ leading, by rw [appendVisible, canonTrap, List.append_assoc]⟩
  | refused issue =>
    obtain ⟨stop, actual, checkAt, canonAt, checkTracks, canonTracks⟩ := status
    exact ⟨stop, actual, checkAt, canonAt, fun depth => (leftTracks depth).append (checkTracks depth),
      fun depth => (rightTracks depth).append (canonTracks depth)⟩
  | returned result =>
    obtain ⟨paired, checkAt, canonAt, checkTracks, canonTracks, kept⟩ := status
    exact ⟨paired, checkAt, canonAt, fun depth => (leftTracks depth).append (checkTracks depth),
      fun depth => (rightTracks depth).append (canonTracks depth), kept⟩

private theorem nominalElements (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (nominal : ∀ item ∈ entries, CanonicalHandle item) (stride ptr index : Nat)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (checkAt : left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width entries stride ptr index >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
      (destination.context inst) destination.width entries .value stride ptr >>= canonNext)) :
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (ElementStop destination inst entries stride ptr canonNext) := by
  induction entries generalizing ptr index left right check canon with
  | nil =>
    simp only [Record.Effects.elements, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] at checkAt canonAt
    exact ⟨canon, .returned (), [], [], left, right, .refl _, .refl _, frame.store, rfl,
      frame, checkAt, canonAt, fun depth => .done _ _, fun depth => .done _ _, trivial⟩
  | cons item rest ih =>
    let checkTail : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)) := fun verdict =>
      (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst)
          destination.width rest stride (ptr + stride) (index + 1)) >>= checkNext
    let canonTail : Unit → Session grow sig (Ret (core3 grow)) := fun _ =>
      CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width rest .value stride (ptr + stride) >>= canonNext
    have atHead : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width item index (.memory ptr) >>= checkTail) := by
      rw [checkAt, Record.Effects.elements]
      congr 1
      simp only [Prog.bind_eq, Prog.bind_assoc, checkTail]
      congr 1
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok value => cases value; rfl
    have atCanonHead : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width item (.memory ptr) >>= canonTail) := by
      rw [canonAt, CanonicalTree.elements]
      congr 1
      change Prog.bind (Prog.bind _ (fun _ => _)) canonNext = Prog.bind _ canonTail
      exact Prog.bind_assoc _ _ _
    have leaf := LinkedCallback.ChildFrameOver.handle_field_then_between
      (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst item (nominal item (by simp))
      index (.memory ptr) checkTail canonTail frame (Core3.Grows.refl _) atHead atCanonHead
      (next := fun _ lhs rhs check canon => CollectionSegment profile ready base bindings older lhs rhs check checkNext canonNext 0
        (ElementStop destination inst rest stride (ptr + stride) canonNext))
      (fun _ reached reference _ _ related _ lhs rhs => ih (fun child member => nominal child (List.mem_cons_of_mem _ member))
        (ptr + stride) (index + 1) related (by exact lhs) (by exact rhs))
    unfold LinkedCallback.HandleFieldThenBetween at leaf
    cases live : liveLeafPlan left.store left.host.writer index item with
    | error issue =>
      rw [live] at leaf
      obtain ⟨labels, tau, tracks⟩ := leaf
      exact ⟨canon, .refused issue, labels, [], _, right, (prefix_survives (tracks 0)).1, .refl _,
        frame.store, silent tau, _, ⟨[], item :: rest, rfl, by simp, by simp⟩, rfl, canonAt, tracks, fun depth => .done _ _⟩
    | ok plan =>
      rw [live] at leaf
      obtain ⟨store, result, initial, leftLabels, rightLabels, quiet, seenLeft, seenRight, runLeft, runRight, success⟩ := leaf
      cases result with
      | error reason =>
        have seen := leafTrap seenRight
        exact ⟨canon, .trapped reason, _, _, _, _, runLeft, runRight, rfl,
          by rw [appendVisible, silent quiet, List.nil_append, leafTrap seenLeft, seen], rfl, rfl, [], seen⟩
      | ok value =>
        cases value
        obtain ⟨leftTracks, rightTracks, next⟩ := success () rfl
        obtain ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, tailLeft, tailRight, same, seen, status⟩ := next
        have leftRun := appendRun runLeft tailLeft
        have rightRun := appendRun runRight tailRight
        have observed : visible ((initial ++ leftLabels) ++ lhs) = visible (rightLabels ++ rhs) := by
          rw [appendVisible, appendVisible, appendVisible, silent quiet, leafSilent seenLeft, leafSilent seenRight,
            List.nil_append, List.nil_append, List.nil_append, seen]
        refine ⟨reached, outcome, _, _, finalLeft, finalRight, leftRun, rightRun, same, observed, ?_⟩
        cases outcome with
        | returned value =>
          obtain ⟨paired, leftAt, rightAt, leftTail, rightTail, kept⟩ := status
          exact ⟨paired, leftAt, rightAt, fun depth => (leftTracks depth).append (leftTail depth),
            fun depth => (rightTracks depth).append (rightTail depth), kept⟩
        | refused issue =>
          obtain ⟨stop, ⟨leading, remaining, split, nonempty, stopAt⟩, leftAt, rightAt, leftTail, rightTail⟩ := status
          refine ⟨stop, ⟨item :: leading, remaining, congrArg (item :: ·) split, nonempty, ?_⟩, leftAt, rightAt,
            fun depth => (leftTracks depth).append (leftTail depth), fun depth => (rightTracks depth).append (rightTail depth)⟩
          simpa only [List.length_cons, Nat.succ_mul, Nat.add_assoc, Nat.add_comm stride] using stopAt
        | trapped reason =>
          obtain ⟨leftEmpty, rightEmpty, before, trapped⟩ := status
          exact ⟨leftEmpty, rightEmpty, before, by rw [appendVisible, leafSilent seenRight, List.nil_append, trapped]⟩

private theorem finishElements (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (mode : CanonicalTree.EntryMode) (output : Stored.Lower.Output) (index ptr : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (checkAt : left.ctl = check.control (checkedCollectionTail destination inst entries area index output ptr (.ok ()) >>= checkNext))
    (canonAt : right.ctl = canon.control (canonicalCollectionTail destination inst entries area output ptr mode >>= canonNext))
    (stopsAt : (Unit → Session grow sig (Ret (core3 grow))) → Session grow sig (Ret (core3 grow)) → Prop)
    (visit : ∀ (checkTail : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
        (canonTail : Unit → Session grow sig (Ret (core3 grow))),
      left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width entries area.size ptr 0 >>= checkTail) →
      right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
        (destination.context inst) destination.width entries mode area.size ptr >>= canonTail) →
      CollectionSegment profile ready base bindings older left right check checkTail canonTail 0 (stopsAt canonTail)) :
    let publish := (ListLower.publish (destination.context inst) destination.width ptr entries.length output : Session grow sig output.Result)
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (stopsAt (fun _ => publish >>= canonNext)) := by
  intro publish
  let onChecked : output.Result → Session grow sig (Ret (core3 grow)) := fun result => checkNext (.ok result)
  let checkTail := checkedSequenceNext (.nested index) (fun (_ : Unit) => publish >>= fun result => pure (.ok result)) checkNext
  let canonTail : Unit → Session grow sig (Ret (core3 grow)) := fun _ => publish >>= canonNext
  have checkElements : left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width entries area.size ptr 0 >>= checkTail) := by
    rw [checkAt]
    congr 1
    simp only [checkedCollectionTail, Prog.bind_eq, Prog.bind_assoc, checkTail, publish]
    congr 1
    funext verdict
    cases verdict with
    | error _ => rfl
    | ok value => cases value; rfl
  have canonElements : right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
      (destination.context inst) destination.width entries mode area.size ptr >>= canonTail) := by
    rw [canonAt]
    congr 1
    change Prog.bind (Prog.bind _ (fun _ => publish)) canonNext = Prog.bind _ canonTail
    exact Prog.bind_assoc _ _ _
  obtain ⟨reached, outcome, lhs, rhs, middleLeft, middleRight, runLeft, runRight, same, seen, status⟩ :=
    visit checkTail canonTail checkElements canonElements
  cases outcome with
  | trapped reason => exact ⟨reached, .trapped reason, lhs, rhs, _, _, runLeft, runRight, same, seen, status⟩
  | refused issue =>
    obtain ⟨stop, witness, leftAt, rightAt, tracksLeft, tracksRight⟩ := status
    exact ⟨reached, .refused (.nested index issue), lhs, rhs, _, _, runLeft, runRight, same, seen,
      stop, witness, leftAt, rightAt, tracksLeft, tracksRight⟩
  | returned value =>
    cases value
    obtain ⟨paired, leftAt, rightAt, tracksLeft, tracksRight, _⟩ := status
    have leftPublish : middleLeft.ctl = check.control (publish >>= onChecked) := by
      rw [leftAt]
      simp only [checkTail, checkedSequenceNext, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind', onChecked]
    obtain ⟨store, result, labels, observed, leftWrites, rightWrites, tracks⟩ :=
      collection_descriptor_cut_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
        (reference := specDispatch ready (LiveDispatch.host bindings base)) (destination.context inst) destination.width
        output ptr entries.length middleLeft middleRight check reached onChecked canonNext same leftPublish rightAt
    have labelMatch : visible (lhs ++ labels) = visible (rhs ++ labels) := by rw [appendVisible, appendVisible, seen]
    have leftRun := appendRun runLeft leftWrites.steps
    have rightRun := appendRun runRight rightWrites.steps
    cases result with
    | error reason =>
      exact ⟨reached, .trapped reason, _, _, _, _, leftRun, rightRun, rfl, labelMatch, rfl, rfl, visible rhs,
        by rw [appendVisible, leafTrap observed]⟩
    | ok descriptor =>
      exact ⟨reached, .returned descriptor, _, _, _, _, leftRun, rightRun, rfl, labelMatch,
        ⟨rfl, paired.pending, paired.results, paired.cancels, paired.blocked, paired.thread, paired.frames, paired.rest⟩,
        rfl, rfl, fun depth => (tracksLeft depth).append (tracks descriptor rfl depth).1,
        fun depth => (tracksRight depth).append (tracks descriptor rfl depth).2, trivial⟩

private theorem rangeThenUnless (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (mode : CanonicalTree.EntryMode)
    (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) (paused : Prop) :
    let area := layout destination.width element
    let lhs := fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext
    let rhs := fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext
    stopsAt (rhs pointer) →
    (∀ bytes (left right : Config (core3 grow) (HostState sig)) (canon : Cursor (E := core3 grow) (HostState sig)),
      (core3 grow).memAddrType? left.store.core destination.memory = some destination.width →
      (core3 grow).memSize? left.store.core destination.memory = some bytes →
      pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
      LinkedCallback.ChildFrameOver older left right check canon →
      left.ctl = check.control (lhs pointer (.ok ())) → right.ctl = canon.control (rhs pointer) →
      ∀ leftLabels rightLabels,
        RetainsBelowTop profile ready (specDispatch ready base) checked leftLabels left →
        RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical rightLabels right →
        visible leftLabels = visible rightLabels →
        CollectionSegment profile ready base bindings older left right check checkNext canonNext 0 stopsAt ∨ paused) →
    CollectionRangeCut profile ready base bindings older checked canonical check destination area entries.length pointer
      (Field.listObjects entries) lhs rhs →
    CollectionSegment profile ready base bindings older checked canonical check checkNext canonNext 1 stopsAt ∨ paused := by
  intro area lhs rhs acceptsInitial visit cut
  obtain ⟨canon, bytes, width, sized, frame, range⟩ := cut
  have trapped (reason : TrapReason)
      (checkRun : ∃ steps, Steps profile ready (specDispatch ready base) checked
        (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg checked))
      (canonRun : ∃ steps, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical
        (List.replicate steps .tau ++ [.trap reason]) (StepDefs.trapCfg canonical)) :
      CollectionSegment profile ready base bindings older checked canonical check checkNext canonNext 1 stopsAt := by
    obtain ⟨leftCount, left⟩ := checkRun
    obtain ⟨rightCount, right⟩ := canonRun
    have seen (count : Nat) : visible (List.replicate count (.tau : Label (core3 grow) (HostState sig)) ++ [.trap reason]) =
        [.trap reason] := by
      rw [show visible (List.replicate count .tau ++ [.trap reason] : Trace grow sig) =
        visible (List.replicate count .tau) ++ visible [.trap reason] from List.filter_append ..,
        silent (labels := List.replicate count .tau)
        (fun _ member => List.eq_of_mem_replicate member)]
      rfl
    exact ⟨canon, .trapped reason, _, _, _, _, left, right,
      congrArg StepDefs.lockdownSt frame.store, (seen leftCount).trans (seen rightCount).symm, rfl, rfl, [], seen rightCount⟩
  by_cases aligned : pointer = alignTo pointer area.alignment
  · simp only [ite_eq_right (not_not_intro aligned)] at range
    by_cases bounds : pointer + entries.length * area.size ≤ bytes
    · simp only [ite_eq_left bounds] at range
      obtain ⟨⟨leading, checkTau, checkRun⟩, ⟨referenceLabels, canonTau, canonRun⟩⟩ := range
      let other := { canonical with ctl := canon.control (rhs pointer) }
      have prefixSeen : visible leading = visible referenceLabels := (silent checkTau).trans (silent canonTau).symm
      cases prepared : Stored.OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) with
      | error issue =>
        rw [prepared] at checkRun
        let refused := LinkedCallback.CollectionVisit.afterAllocation index issue
        have stop : lhs pointer (.error issue) = checkNext (.error refused) := by cases issue <;> rfl
        rw [stop] at checkRun
        exact .inl ⟨canon, .refused refused, _, _, _, other, (prefix_survives (checkRun 0)).1,
          (prefix_survives (canonRun 0)).1, frame.store, prefixSeen, rhs pointer, acceptsInitial, rfl, rfl, checkRun, canonRun⟩
      | ok result =>
        cases result
        rw [prepared] at checkRun
        let entered := { checked with ctl := check.control (lhs pointer (.ok ())) }
        have child : LinkedCallback.ChildFrameOver older entered other check canon :=
          ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        rcases visit bytes entered other canon width sized aligned bounds child rfl rfl leading referenceLabels checkRun canonRun prefixSeen with
          ⟨reached, outcome, checkedTail, canonTail, leftEnd, rightEnd, checkedRun, canonicalRun, same, seen, result⟩ | later
        · have left := appendRun (prefix_survives (checkRun 0)).1 checkedRun
          have right := appendRun (prefix_survives (canonRun 0)).1 canonicalRun
          have labels : visible (leading ++ checkedTail) = visible (referenceLabels ++ canonTail) := by
            rw [appendVisible, appendVisible, prefixSeen, seen]
          refine .inl ⟨reached, outcome, _, _, leftEnd, rightEnd, left, right, same, labels, ?_⟩
          cases outcome with
          | returned value =>
            obtain ⟨paired, leftAt, rightAt, leftTail, rightTail, kept⟩ := result
            exact ⟨paired, leftAt, rightAt, fun depth => (checkRun depth).append (leftTail depth),
              fun depth => (canonRun depth).append (rightTail depth), kept⟩
          | refused issue =>
            obtain ⟨stop, accepted, leftAt, rightAt, leftTail, rightTail⟩ := result
            exact ⟨stop, accepted, leftAt, rightAt, fun depth => (checkRun depth).append (leftTail depth),
              fun depth => (canonRun depth).append (rightTail depth)⟩
          | trapped reason =>
            obtain ⟨leftDone, rightDone, before, tail⟩ := result
            exact ⟨leftDone, rightDone, visible referenceLabels ++ before,
              by rw [appendVisible, tail, List.append_assoc]⟩
        · exact .inr later
    · simp only [ite_eq_right bounds] at range
      exact .inl (trapped .outOfBounds range.1 range.2)
  · simp only [ite_eq_left aligned] at range
    exact .inl (trapped .unalignedPointer range.1 range.2)

private theorem rangeThen (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (mode : CanonicalTree.EntryMode)
    (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    (stopsAt : Session grow sig (Ret (core3 grow)) → Prop) :
    let area := layout destination.width element
    let lhs := fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext
    let rhs := fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext
    stopsAt (rhs pointer) →
    (∀ bytes (left right : Config (core3 grow) (HostState sig)) (canon : Cursor (E := core3 grow) (HostState sig)),
      (core3 grow).memAddrType? left.store.core destination.memory = some destination.width →
      (core3 grow).memSize? left.store.core destination.memory = some bytes →
      pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
      LinkedCallback.ChildFrameOver older left right check canon →
      left.ctl = check.control (lhs pointer (.ok ())) → right.ctl = canon.control (rhs pointer) →
      CollectionSegment profile ready base bindings older left right check checkNext canonNext 0 stopsAt) →
    CollectionRangeCut profile ready base bindings older checked canonical check destination area entries.length pointer
      (Field.listObjects entries) lhs rhs →
    CollectionSegment profile ready base bindings older checked canonical check checkNext canonNext 1 stopsAt := by
  intro area lhs rhs accepts visit cut
  exact (rangeThenUnless destination inst element entries mode output index pointer checkNext canonNext stopsAt False accepts
    (fun bytes left right canon width sized aligned bounds paired lhsAt rhsAt _ _ _ _ _ =>
      .inl (visit bytes left right canon width sized aligned bounds paired lhsAt rhsAt)) cut).resolve_right id

private theorem localTail (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (mode : CanonicalTree.EntryMode) (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)} :
    let area := layout destination.width element
    let lhs := fun addr verdict => checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext
    let rhs := fun addr => canonicalCollectionTail destination inst entries area output addr mode >>= canonNext
    (∀ bytes (left right : Config (core3 grow) (HostState sig)) (canon : Cursor (E := core3 grow) (HostState sig)),
      (core3 grow).memAddrType? left.store.core destination.memory = some destination.width →
      (core3 grow).memSize? left.store.core destination.memory = some bytes →
      pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
      left.store = right.store → check.thread = canon.thread → left.ctl = check.control (lhs pointer (.ok ())) →
      right.ctl = canon.control (rhs pointer) →
      LocalCutKeepingBetween profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base))
        (fun store => Core3.Grows left.store.core store.core) left right check canon (fun value => checkNext (.ok value)) canonNext) →
    CollectionRangeCut profile ready base bindings older checked canonical check destination area entries.length pointer
      (Field.listObjects entries) lhs rhs →
    CollectionReturn profile ready base bindings older checked canonical check checkNext canonNext (rhs pointer) := by
  intro area lhs rhs visit cut
  refine rangeThen destination inst element entries mode output index pointer checkNext canonNext _ rfl ?_ cut
  intro bytes left right canon width sized aligned bounds frame checkAt canonAt
  obtain ⟨store, outcome, checkedTail, canonTail, checkedRun, canonicalRun, seen, result⟩ :=
    visit bytes left right canon width sized aligned bounds frame.store frame.thread checkAt canonAt
  cases outcome with
  | ok value =>
    exact ⟨canon, .returned value, _, _, _, _, checkedRun, canonicalRun.steps, rfl, seen,
      ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩,
      rfl, rfl, result.2.1, result.2.2, trivial⟩
  | error reason =>
    exact ⟨canon, .trapped reason, _, _, _, _, checkedRun, canonicalRun.steps, rfl, seen, rfl, rfl, result⟩

private theorem appendReplyTrack {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start before after : Config (core3 grow) (HostState sig)} {body reply : Trace grow sig} {offset : Nat}
    (tracks : ∀ depth, Prefix profile ready dispatch start (.active 0 (depth + offset)) body before (.active 0 depth))
    (pop : ∀ place, Trail profile ready dispatch before (some place) reply after
      ((Edit.pop : Edit (core3 grow) (HostState sig)).follow place)) :
    ∀ depth, Prefix profile ready dispatch start (.active 0 (depth + 1 + offset)) (body ++ reply) after (.active 0 depth) := by
  intro depth
  have moved : Trail profile ready dispatch before (some (.active 0 (depth + 1))) reply after (some (.active 0 depth)) := pop _
  obtain ⟨place, same, tail⟩ := moved.survives
  cases same
  exact (tracks (depth + 1)).append tail

theorem replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    {callerLabels stopsAt offset}
    (caller : Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) callerLabels checked (.active 0 offset))
    (cut : CollectionSegment profile ready base bindings older checked canonical check site.reply site.referenceReply offset stopsAt)
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True)
    (next : ∀ left right, HostFrame.Related.Paired older left right → afterReturn left right := by intros; trivial) :
    CollectionSegmentReplies profile ready base bindings older site checked canonical stopsAt offset afterReturn := by
  obtain ⟨canon, outcome, lhs, rhs, left, right, checkedRun, canonRun, same, seen, result⟩ := cut
  have silentTail (trace suffix : Trace grow sig) (tau : visible suffix = []) : visible (trace ++ suffix) = visible trace := by
    change List.filter _ (trace ++ suffix) = _
    rw [List.filter_append]
    change visible trace ++ visible suffix = _
    rw [tau, List.append_nil]
  cases outcome with
  | trapped reason => exact ⟨.trapped reason, lhs, rhs, left, right, checkedRun, canonRun, same, seen, result⟩
  | returned value =>
    obtain ⟨frame, checkAt, canonAt, tracks, canonTracks, _⟩ := result
    obtain ⟨checkEnd, canonEnd, checkReply, canonReply, stores, checkHost, canonHost, paired, checkPop, canonPop⟩ :=
      LinkedCallback.MemorySequence.resume_returned_give site value frame
        (caller.append (by simpa only [Nat.zero_add] using tracks 0)) checkAt canonAt
    exact ⟨.returned value, _, _, checkEnd, canonEnd, appendRun checkedRun (checkReply _), appendRun canonRun (canonReply _),
      stores, by rw [silentTail _ _ rfl, silentTail _ _ rfl, seen], left, right, lhs, rhs, rfl, rfl,
      checkedRun, canonRun, checkReply, canonReply, checkHost, canonHost, paired, next _ _ paired,
      appendReplyTrack tracks (checkPop _), appendReplyTrack canonTracks (canonPop _)⟩
  | refused issue =>
    obtain ⟨stop, stopped, checkAt, canonAt, tracks, canonTracks⟩ := result
    obtain ⟨segments, callerAt⟩ := site.reached_caller checkAt (caller.append (by simpa only [Nat.zero_add] using tracks 0))
    let reply := route.reply site.destination site.start.host.nextTicket (.error issue)
    have atReply : left.ctl = ⟨check.thread, .prog (do return .flat (← writeCompletion reply)),
        .core site.core site.resume :: segments⟩ :: check.rest := by
      simpa only [Cursor.control, callerAt, PayloadRoot.Site.reply, reply] using checkAt
    let finished := { left with
      host := left.host.record reply.1
      ctl := ⟨check.thread, .core ((core3 grow).resume left.store.core site.core (.values reply.2)) site.resume, segments⟩ :: check.rest }
    have resumes (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) :
        Steps profile ready dispatch left [.tau, .tau, .tau] finished := Plain.give_completion_steps reply atReply
    exact ⟨.refused issue, _, rhs, finished, right, appendRun checkedRun (resumes _), canonRun, same,
      by rw [silentTail _ _ rfl, seen], left, lhs, canon, stop, stopped, rfl, checkedRun, canonTracks, rfl, resumes, canonAt,
      appendReplyTrack tracks (fun place => Plain.give_completion_trail reply place atReply)⟩

theorem rejoinPublished {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical left right : Config (core3 grow) (HostState sig)}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {callerLabels seen offset}
    (caller : Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) callerLabels checked (.active 0 offset))
    (leading : ComparedSlots profile ready base bindings checked canonical seen left right offset)
    (publish : LiveValueCommit profile ready base bindings route.output site.reply site.referenceReply
      (fun _ => LinkedCallback.ChildFrameOver older) left right check canon) :
    CollectionSegmentReplies profile ready base bindings older site checked canonical (fun _ => False) offset := by
  obtain ⟨checkLabels, canonLabels, checkTracks, canonTracks, checkSeen, canonSeen⟩ := leading
  have terminal : CollectionSegment profile ready base bindings older left right check site.reply site.referenceReply 0
      (fun _ => False) := by
    obtain ⟨store, outcome, labels, observed, lhs, rhs, continuation⟩ := publish
    cases outcome with
    | error reason =>
      exact ⟨canon, .trapped reason, labels, labels, _, _, lhs.steps, rhs.steps, rfl, rfl, rfl, rfl, [], leafTrap observed⟩
    | ok value =>
      obtain ⟨keepsLeft, keepsRight, frame⟩ := continuation value rfl
      exact ⟨canon, .returned value, labels, labels, _, _, lhs.steps, rhs.steps, rfl, rfl, frame,
        rfl, rfl, keepsLeft, keepsRight, trivial⟩
  exact replies site caller (prependSegment checkTracks canonTracks (checkSeen.trans canonSeen.symm) terminal)

private theorem listEntries {entries : List Field} {element schema : Stored.TypeOf}
    (matched : Field.LayoutMatches (.dynamic (.list element) element entries) schema) : Field.EntriesMatch entries element := by
  cases matched with
  | list children => exact children

private theorem nominalEntry {item : Field} {element : Stored.TypeOf}
    (nominal : NominalElement element) (shape : item.LayoutMatches element) (emitted : item.Emitted) : CanonicalHandle item := by
  cases item with
  | owner | endpoint | context => trivial
  | data => cases nominal <;> cases shape <;> cases emitted
  | aggregate | fixed | dynamic | sum => cases nominal <;> cases shape

private theorem listCompiled {item : Field} {element : Stored.TypeOf} (matched : item.LayoutMatches (.list element))
    (emitted : item.Emitted) : ∃ entries, item = .dynamic (.list element) element entries ∧
      Field.EntriesMatch entries element ∧ ∀ entry ∈ entries, entry.Emitted := by
  cases emitted with
  | list children =>
    cases matched with
    | list matching => exact ⟨_, rfl, matching, children⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | primitive | enum | flags | context | owner | aggregate | fixed | map | sum => cases matched

private def PlacedFieldRule (compare : FieldComparison grow sig)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (destination : RecordDestination) (inst : InstId) (item : Field) (address : Nat) : Prop :=
  ∀ index (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) left right check canon,
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core left.store.core →
    (core3 grow).memAddrType? left.store.core destination.memory = some destination.width →
    placement destination left.store (layout destination.width item.type) address = .ok () →
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width item index (.memory address) >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width item (.memory address) >>= canonNext) →
    ∀ finish : Finish grow sig, (∀ reached reference check canon, LinkedCallback.ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon) →
    compare item index address left right check canon checkNext canonNext finish

private theorem placedFieldOfRule {compare : FieldComparison grow sig} {older origin destination inst item address}
    (rule : FieldRule compare older origin destination inst item address) :
    PlacedFieldRule compare older origin destination inst item address :=
  fun index checkNext canonNext left right check canon frame growth _ _ =>
    rule index checkNext canonNext left right check canon frame growth

private theorem liveElementsRule (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (index basePtr count position bytes : Nat) (compare : FieldComparison grow sig)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) (origin : CStore (core3 grow))
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width element).alignment)
    (bounds : basePtr + count * (layout destination.width element).size ≤ bytes)
    (remaining : position + entries.length ≤ count)
    (shapes : ∀ item ∈ entries, item.type = element)
    (children : ∀ item ∈ entries, ∀ address, PlacedFieldRule compare older origin destination inst item address)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    (done : ∀ left right check canon, LinkedCallback.ChildFrameOver older left right check canon →
      Core3.Grows origin.core left.store.core → left.ctl = check.control (checkNext (.ok ())) →
      right.ctl = canon.control (canonNext ()) → finish left right check canon)
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core) :
    let stride := (layout destination.width element).size
    let pointer := basePtr + position * stride
    left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width entries stride pointer index >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none
      (destination.context inst) destination.width entries .value stride pointer >>= canonNext) →
    liveElements destination inst stride compare checkNext canonNext finish entries index pointer left right check canon := by
  induction entries generalizing index position left right check canon with
  | nil =>
    intro _ _ checkAt canonAt
    exact done left right check canon frame growth checkAt canonAt
  | cons item rest ih =>
    intro stride pointer checkAt canonAt
    let checked := checkTail (.elements stride) destination inst rest (index + 1) (pointer + stride) checkNext
    let canonical := canonTail (.elements stride) destination inst rest (pointer + stride) canonNext
    have checkHead : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width item index (.memory pointer) >>= checked) := by
      rw [checkAt, Record.Effects.elements]
      congr 1
      simp only [Prog.bind_eq, Prog.bind_assoc, checked]
      congr 1
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok value => cases value; rfl
    have canonHead : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width item (.memory pointer) >>= canonical) := by
      rw [canonAt, CanonicalTree.elements]
      congr 1
      change Prog.bind (Prog.bind _ (fun _ => _)) canonNext = Prog.bind _ canonical
      exact Prog.bind_assoc _ _ _
    have valid : position < count := Nat.lt_of_lt_of_le (by simp) remaining
    have placed : placement destination left.store (layout destination.width item.type) pointer = .ok () := by
      rw [shapes item (by simp)]
      exact (list_entry_placement_of_growth destination inst element growth width sized aligned bounds valid).2
    refine children item (by simp) pointer index checked canonical left right check canon frame growth
      (growth.memAddrType width) placed checkHead canonHead _ ?_
    intro lhs rhs checkCursor canonCursor related grown checkedAt canonicalAt
    have nextPointer : basePtr + (position + 1) * (layout destination.width element).size = pointer + stride := by
      simp only [pointer, stride, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    rw [← nextPointer]
    exact ih (index + 1) (position + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using remaining)
      (fun child member => shapes child (.tail _ member)) (fun child member => children child (.tail _ member))
      related grown
      (by simpa only [checked, checkTail, Track.checked, pointer, stride, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using checkedAt)
      (by simpa only [canonical, canonTail, Track.canonical, pointer, stride, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using canonicalAt)

private theorem livePublish (destination : RecordDestination) (inst : InstId) (pointer count : Nat)
    (output : Stored.Lower.Output) (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (finish : ValueFinish grow sig output) {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)}
    (done : ∀ value left right check canon, LinkedCallback.ChildFrameOver older left right check canon →
      Core3.Grows origin.core left.store.core → left.ctl = check.control (checkNext (.ok value)) →
      right.ctl = canon.control (canonNext value) → finish value left right check canon)
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (paired : LinkedCallback.ChildFrameOver older left right check canon) (kept : Core3.Grows origin.core left.store.core)
    (leftAt : left.ctl = check.control (ListLower.publish (destination.context inst) destination.width pointer count output >>= fun value => checkNext (.ok value)))
    (rightAt : right.ctl = canon.control (ListLower.publish (destination.context inst) destination.width pointer count output >>= canonNext)) :
    LiveListPublish profile ready base bindings output checkNext canonNext finish left right check canon := by
  obtain ⟨store, result, labels, observed, lhsRun, rhsRun, tracks⟩ :=
    collection_descriptor_cut_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) (destination.context inst) destination.width
      output pointer count left right check canon (fun value => checkNext (.ok value)) canonNext paired.store leftAt rightAt
  refine ⟨store, result, labels, observed, lhsRun, rhsRun, ?_⟩
  intro value returned
  have chain := kept.trans lhsRun.grows
  subst result
  exact ⟨fun depth => (tracks value rfl depth).1, fun depth => (tracks value rfl depth).2,
    done value _ _ check canon ⟨rfl, paired.pending, paired.results, paired.cancels, paired.blocked, paired.thread,
      paired.frames, paired.rest⟩ chain rfl rfl⟩

private theorem collectionElementFoci (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (mode : CanonicalTree.EntryMode) (output : Stored.Lower.Output) (pointer index : Nat)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    {lhs rhs : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (checkAt : lhs.ctl = check.control (checkedCollectionTail destination inst entries area index output pointer (.ok ()) >>= checkNext))
    (canonAt : rhs.ctl = canon.control (canonicalCollectionTail destination inst entries area output pointer mode >>= canonNext)) :
    lhs.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width entries area.size pointer 0 >>= publishChecked destination inst pointer entries.length index output checkNext) ∧
    rhs.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width
      entries mode area.size pointer >>= publishCanonical destination inst pointer entries.length output canonNext) := by
  constructor
  · rw [checkAt]
    congr 1
    simp only [checkedCollectionTail, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext verdict
    cases verdict with
    | error _ => rfl
    | ok result => cases result; simp only [publishChecked, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
  · rw [canonAt]
    congr 1
    exact Prog.bind_assoc _ _ _

private theorem liveListVisitor (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output) (compare : FieldComparison grow sig)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin initial : CStore (core3 grow)) (growth : Core3.Grows origin.core initial.core)
    (shapes : Field.EntriesMatch entries element)
    (children : ∀ item ∈ entries, ∀ reached address, PlacedFieldRule compare older reached destination inst item address)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (finish : ValueFinish grow sig output)
    (done : ∀ value left right check canon, LinkedCallback.ChildFrameOver older left right check canon →
      Core3.Grows origin.core left.store.core → left.ctl = check.control (checkNext (.ok value)) →
      right.ctl = canon.control (canonNext value) → finish value left right check canon) :
    CollectionVisitor destination inst (.list element) element entries index output checkNext canonNext older initial
      (liveListTail profile ready base bindings destination inst element entries index output compare checkNext canonNext finish) := by
  intro pointer bytes lhs rhs check canon frame grown width sized aligned bounds checkAt canonAt
  let area := layout destination.width element
  let checked := publishChecked destination inst pointer entries.length index output checkNext
  let canonical := publishCanonical destination inst pointer entries.length output canonNext
  obtain ⟨checkElements, canonElements⟩ := collectionElementFoci destination inst entries area
    (CanonicalTree.EntryMode.forOutput destination.width (.list element) output) output pointer index checkNext canonNext checkAt canonAt
  have mode : CanonicalTree.EntryMode.forOutput destination.width (.list element) output = .value := by
    cases output <;> rfl
  have publish := fun left right cursor peer paired kept leftAt rightAt =>
    livePublish (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst pointer entries.length output checkNext canonNext finish done
      (left := left) (right := right) (check := cursor) (canon := peer) paired (growth.trans (grown.trans kept)) leftAt rightAt
  simpa only [liveListTail, Nat.zero_mul, Nat.add_zero] using
    liveElementsRule destination inst element entries 0 pointer entries.length 0 bytes compare older lhs.store
      width sized aligned bounds (Nat.zero_add _).le
      (fun item member => (entries_match_of_mem shapes member).type_eq) (fun item member => children item member lhs.store)
      checked canonical _ publish frame (Core3.Grows.refl _)
      (by simpa only [Nat.zero_mul, Nat.add_zero] using checkElements)
      (by simpa only [Nat.zero_mul, Nat.add_zero, mode] using canonElements)

private theorem nominalListRule (destination : RecordDestination) (inst : InstId) (depth : Nat)
    {schema : Stored.TypeOf} (family : NominalListType depth schema) (item : Field) (address : Nat)
    (matched : item.LayoutMatches schema) (emitted : item.Emitted)
    {origin : CStore (core3 grow)}
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} :
    FieldRule (liveNominalList profile ready base bindings older destination inst depth) older origin destination inst item address := by
  induction depth generalizing schema item address origin with
  | zero =>
    cases family with
    | leaf nominal =>
      intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
      exact LinkedCallback.ChildFrameOver.handle_field_then_between destination inst item (nominalEntry nominal matched emitted)
        index (.memory address) checkNext canonNext frame growth checkAt canonAt (fun _ => ends)
  | succ depth ih =>
    cases family with
    | @list _ element family =>
      obtain ⟨entries, rfl, shapes, compiled⟩ := listCompiled matched emitted
      intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
      exact ⟨element, entries, rfl, collectionEntryVisiting destination inst (.list element) element entries index (.memory address)
        checkNext canonNext frame checkAt canonAt embedder _
          (liveListVisitor destination inst element entries index (.memory address) _ older origin left.store growth
            shapes (fun child member _ slot => placedFieldOfRule
              (ih family child slot (entries_match_of_mem shapes member) (compiled child member)))
            checkNext canonNext (fun () => finish) (fun _ => ends)) (initialSlots left right)⟩

private theorem mapPlacement (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType)
    (element : Stored.TypeOf) (output : Stored.Lower.Output)
    (before : Config (core3 grow) (HostState sig)) (canon : Cursor (E := core3 grow) (HostState sig))
    (next : AddrType → Session grow sig (Ret (core3 grow)))
    (width : (core3 grow).memAddrType? before.store.core destination.memory = some destination.width)
    (atPlacement : before.ctl = canon.control (mapFieldPlacement (destination.context inst)
      (CanonicalTree.EntryMode.forOutput destination.width (.map key element) output) next)) :
    ∃ labels, visible labels = [] ∧ ReturnFrame.Occurrence.RetainsActiveSlots profile ready
      (specDispatch ready (LiveDispatch.host bindings base)) before labels
      { before with ctl := canon.control (next destination.width) } := by
  cases output with
  | memory address =>
    have same : before = { before with ctl := canon.control (next destination.width) } := by
      cases before
      simp_all [mapFieldPlacement, CanonicalTree.EntryMode.forOutput]
    exact ⟨[], rfl, fun depth => same ▸ .done before (.active 0 depth)⟩
  | flat =>
    have reached : ptrTypeIn before.store (destination.context inst) = destination.width := by
      simp [ptrTypeIn, RecordDestination.context, CanonOpts.ptrType, width]
    refine ⟨[.tau], rfl, fun depth => ?_⟩
    change before.ctl = canon.control (.op .get (fun store => next (ptrTypeIn store (destination.context inst)))) at atPlacement
    simpa only [reached, Cursor.control] using (ReturnFrame.Occurrence.Prefix.read (profile := profile)
      (ready := ready) (dispatch := specDispatch ready (LiveDispatch.host bindings base)) depth atPlacement)

theorem stringMapKey (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value root : Field) {schema : Stored.TypeOf}
    (layoutRoot : root.LayoutMatches schema)
    (fitRoot : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocator : Field.AllocatorFor destination.realloc root)
    (path : Field.Descendant root (.aggregate (.record (mapEntryFields .string element)) [key.field, value]))
    (origin : CStore (core3 grow)) (basePtr bytes count entryIndex issueIndex : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (entry : entryIndex < count)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let cx := destination.context inst
    let type : Stored.TypeOf := .record (mapEntryFields .string element)
    let ptr := basePtr + entryIndex * (layout destination.width type).size
    let keySlot := fun reached => alignTo ptr (layout reached key.field.type).alignment
    let valueSlot := fun keyWidth reached => alignTo
      (keySlot keyWidth + (layout keyWidth key.field.type).size) (layout reached value.type).alignment
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
    let afterKey := fun keyWidth (_ : Unit) => mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory (valueSlot keyWidth reached)) >>= canonNext
    let following := fun verdict : Except RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1
          (.memory (valueSlot destination.width destination.width))) >>= fun result => checkNext (result.mapError (.nested issueIndex))
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [key.field, value]) issueIndex (.memory ptr) >>= checkNext) →
    right.ctl = canon.control (mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width key.field (.memory (keySlot reached)) >>= afterKey reached) →
    StringKeyReplay profile ready base bindings older origin destination inst key (keySlot destination.width) left right check canon
      following (afterKey destination.width) := by
  intro cx type ptr keySlot valueSlot mode afterKey following checkAt canonAt
  let keyPayload : Stored.Payload (.prim .string) := ⟨.string key.value, .string key.valid⟩
  let keyOutput := Stored.Lower.Output.memory (keySlot destination.width)
  have keyPath : Field.Descendant root key.field := path.trans (.aggregate (by simp) (.self _))
  have fit := Field.Descendant.string_pre keyPayload rfl keyPath layoutRoot Quirks.none destination.encoding destination.width fitRoot
  obtain ⟨address, realloc⟩ := allocator key.field keyPath rfl
  have currentWidth := growth.memAddrType width
  obtain ⟨placed, checkTracks⟩ := map_key_placement (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    destination inst .string element keyPayload value origin basePtr bytes count entryIndex width sized aligned bounds entry issueIndex
    left (frame.store ▸ growth) check checkNext checkAt
  obtain ⟨canonLabels, canonQuiet, canonTracks⟩ := mapPlacement (profile := profile) (ready := ready) (base := base)
    (bindings := bindings) destination inst .string element output right canon _ currentWidth canonAt
  let checkKey := { left with ctl := check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
    key.field 0 keyOutput >>= following) }
  let canonKey := { right with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none cx destination.width
    key.field keyOutput >>= afterKey destination.width) }
  obtain ⟨reads, keyLeft, keyRight⟩ := string_plan_entry_between (profile := profile) (ready := ready)
    (dispatch := specDispatch ready base) (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst
    key.value key.valid 0 keyOutput checkKey canonKey check canon following (afterKey destination.width) frame.store currentWidth
    realloc fit placed rfl rfl
  unfold StringKeyReplay StringKeyThen
  refine ⟨[.tau] ++ List.replicate reads .tau, canonLabels ++ [.tau], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [appendVisible, silent (fun _ member => List.eq_of_mem_replicate member)]
    rfl
  · rw [appendVisible, canonQuiet]
    rfl
  · exact fun depth => (checkTracks depth).append (keyLeft depth)
  · exact fun depth => (canonTracks depth).append (keyRight depth)
  · exact ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
  · refine CallbackPrefix.stringReplay (origin := origin) _ 0 _ _ _ ?_ ?_ ?_ ?_ embedder ?_
    · exact ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    · exact frame.store ▸ growth
    · rfl
    · rfl
    · intro pointer lhs rhs cursor peer frame grew checkAt canonAt
      refine ⟨frame, grew, ?_⟩
      exact string_descriptor_cut_between cx destination.width keyOutput _ pointer lhs rhs cursor peer
        (fun result => following (.ok result)) (afterKey destination.width) frame.store checkAt canonAt

private theorem nominalMapValue (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (value : Field) (afterKey issueIndex : Nat)
    (nominal : NominalElement element) (matched : value.LayoutMatches element) (emitted : value.Emitted)
    (origin : CStore (core3 grow)) (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core) :
    let cx := destination.context inst
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    let pending := mapValueProgram destination inst mode value afterKey canonNext
    let valPtr := alignTo afterKey (layout destination.width value.type).alignment
    let report := fun verdict : Except RecordLower.Issue Unit => checkNext (verdict.mapError (.nested issueIndex))
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1
      (.memory valPtr) >>= report) → right.ctl = canon.control pending →
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (· = pending) (fun reached => Core3.Grows origin.core reached.core) := by
  intro cx mode pending valPtr report checkAt canonAt
  let canonBody := fun reached => CanonicalTree.field Limits.spec Quirks.none cx destination.width value
    (.memory (alignTo afterKey (layout reached value.type).alignment)) >>= canonNext
  obtain ⟨placement, quietPlacement, tracksPlacement⟩ := mapPlacement (profile := profile) (ready := ready) (base := base)
    (bindings := bindings) destination inst key element output right canon canonBody
    ((frame.store ▸ growth : Core3.Grows origin.core right.store.core).memAddrType width) canonAt
  let afterPlacement := { right with ctl := canon.control (canonBody destination.width) }
  have placed : LinkedCallback.ChildFrameOver older left afterPlacement check canon :=
    ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
  have leaf := LinkedCallback.ChildFrameOver.handle_field_then_between
    (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst value (nominalEntry nominal matched emitted)
    1 (.memory valPtr) report canonNext placed growth checkAt rfl
    (next := fun _ lhs rhs check canon => LinkedCallback.ChildFrameOver older lhs rhs check canon ∧ Core3.Grows origin.core lhs.store.core)
    (fun _ _ _ _ _ related grown _ _ => ⟨related, grown⟩)
  unfold LinkedCallback.HandleFieldThenBetween at leaf
  cases live : liveLeafPlan left.store left.host.writer 1 value with
  | error issue =>
    rw [live] at leaf
    obtain ⟨labels, quiet, tracks⟩ := leaf
    exact ⟨canon, .refused (.nested issueIndex issue), labels, [], _, right, (prefix_survives (tracks 0)).1, .refl _, frame.store,
      silent quiet, pending, rfl, rfl, canonAt, tracks, fun depth => .done _ _⟩
  | ok plan =>
    rw [live] at leaf
    obtain ⟨store, result, guard, checkLabels, canonLabels, quiet, seenLeft, seenRight, runLeft, runRight, success⟩ := leaf
    have runCanonical := appendRun (prefix_survives (tracksPlacement 0)).1 runRight
    cases result with
    | error reason =>
      refine ⟨canon, .trapped reason, _, _, _, _, runLeft, runCanonical, rfl, ?_, rfl, rfl, [], ?_⟩
      · simp only [appendVisible, silent quiet, quietPlacement, List.nil_append, leafTrap seenLeft, leafTrap seenRight]
      · simp only [appendVisible, quietPlacement, List.nil_append, leafTrap seenRight]
    | ok result =>
      cases result
      obtain ⟨leftTracks, rightTracks, paired, kept⟩ := success () rfl
      refine ⟨canon, .returned (), _, _, _, _, runLeft, runCanonical, rfl, ?_, paired, rfl, rfl, leftTracks,
        fun depth => (tracksPlacement depth).append (rightTracks depth), kept⟩
      simp only [appendVisible, silent quiet, quietPlacement, List.nil_append, leafSilent seenLeft, leafSilent seenRight]

theorem stringKeyNominalValue (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value : Field) (address issueIndex : Nat)
    (nominal : NominalElement element) (matched : value.LayoutMatches element) (emitted : value.Emitted)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)} :
    StringKeyNominalValue profile ready base bindings older origin destination inst element output key value address issueIndex
      left right check canon checkNext canonNext := by
  unfold StringKeyNominalValue
  intro afterKey mode pending place report following reached
  unfold StringKeyReplay StringKeyThen at reached
  unfold StringKeyThen
  obtain ⟨leftLabels, rightLabels, seenLeft, seenRight, tracksLeft, tracksRight, paired, replay⟩ := reached
  refine ⟨leftLabels, rightLabels, seenLeft, seenRight, tracksLeft, tracksRight, paired, CallbackPrefix.stringReplayMap ?_ replay⟩
  intro pointer lhs rhs cursor peer done
  obtain ⟨frame, growth, store, result, labels, observed, leftRun, rightRun, tracks⟩ := done
  cases result with
  | error reason =>
    exact ⟨peer, .trapped reason, _, _, _, _, leftRun.steps, rightRun.steps, rfl, rfl, rfl, rfl, [], leafTrap observed⟩
  | ok result =>
    cases result
    let checkValue := { lhs with store, ctl := cursor.control (following (.ok ())) }
    let canonValue := { rhs with store, ctl := peer.control pending }
    have valueFrame : LinkedCallback.ChildFrameOver older checkValue canonValue cursor peer :=
      ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    have tail := nominalMapValue (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst .string element output value afterKey issueIndex nominal matched emitted origin width checkNext canonNext
      valueFrame (growth.trans leftRun.grows) rfl rfl
    exact prependSegment (fun depth => (tracks () rfl depth).1) (fun depth => (tracks () rfl depth).2) rfl tail

private theorem nominalMapEntry (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output)
    (keyData : LocalDataType (.prim key.toPrimitive)) (keyPayload : Stored.Payload (.prim key.toPrimitive))
    (value : Field) (nominal : NominalElement element) (matched : value.LayoutMatches element) (emitted : value.Emitted)
    (origin : CStore (core3 grow)) (basePtr bytes count entryIndex : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entry : entryIndex < count) (issueIndex : Nat)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core) :
    let cx := destination.context inst
    let type : Stored.TypeOf := .record (mapEntryFields key element)
    let ptr := basePtr + entryIndex * (layout destination.width type).size
    let keyField := Field.data (.prim key.toPrimitive) keyPayload
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    let afterKey := fun (keyWidth : AddrType) (_ : Unit) => mapFieldPlacement cx mode fun reached =>
      let area := layout keyWidth keyField.type
      let address := alignTo (alignTo ptr area.alignment + area.size) (layout reached value.type).alignment
      CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory address) >>= canonNext
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [keyField, value]) issueIndex (.memory ptr) >>= checkNext) →
    right.ctl = canon.control (mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField
        (.memory (alignTo ptr (layout reached keyField.type).alignment)) >>= afterKey reached) →
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (· = afterKey destination.width ()) (fun reached => Core3.Grows origin.core reached.core) := by
  intro cx type ptr keyField mode afterKey checkAt canonAt
  let keyArea := layout destination.width keyField.type
  let keyPtr := alignTo ptr keyArea.alignment
  let valPtr := alignTo (keyPtr + keyArea.size) (layout destination.width value.type).alignment
  let onChecked := fun verdict : Except RecordLower.Issue Unit => checkNext (verdict.mapError (.nested issueIndex))
  let checkValue : Session grow sig (Except RecordLower.Issue Unit) :=
    Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1 (.memory valPtr)
  let canonKeyStart := { right with ctl := canon.control (CanonicalTree.field Limits.spec Quirks.none cx destination.width
    keyField (.memory keyPtr) >>= afterKey destination.width) }
  obtain ⟨headLabels, headQuiet, headTracks⟩ := mapPlacement (profile := profile) (ready := ready) (base := base)
    (bindings := bindings) destination inst key element output right canon _ (growth.memAddrType width) canonAt
  obtain ⟨store, result, checkKey, canonKey, runCheckKey, runCanonKey, keyLabels, keyStatus⟩ :=
    local_map_key_then_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst key element keyData keyPayload value
      origin basePtr bytes count entryIndex width sized aligned bounds entry issueIndex left canonKeyStart growth frame.store
      check canon frame.thread checkNext (afterKey destination.width) checkAt rfl
  have keyRun := appendRun (prefix_survives (headTracks 0)).1 runCanonKey.steps
  have keySeen : visible checkKey = visible (headLabels ++ canonKey) := by
    rw [appendVisible, headQuiet, List.nil_append, keyLabels]
  cases result with
  | error reason =>
    obtain ⟨prior, stopped⟩ := keyStatus
    exact ⟨canon, .trapped reason, _, _, _, _, runCheckKey, keyRun, rfl, keySeen, rfl, rfl, prior,
      by rw [appendVisible, headQuiet, List.nil_append, stopped]⟩
  | ok result =>
    cases result
    obtain ⟨grown, trackedLeft, trackedRight⟩ := keyStatus
    let checked := { left with store, ctl := check.control (checkValue >>= onChecked) }
    let valueStart := { right with store, ctl := canon.control (afterKey destination.width ()) }
    have reached : LinkedCallback.ChildFrameOver older checked valueStart check canon :=
      ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    have tail := nominalMapValue (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst key element output value (keyPtr + keyArea.size) issueIndex nominal matched emitted origin width checkNext canonNext
      reached grown rfl rfl
    exact prependSegment trackedLeft (fun depth => (headTracks depth).append (trackedRight depth)) keySeen tail

theorem refusalReply {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (type element : Stored.TypeOf) (entries : List Field) (index pointer bytes : Nat)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    {leading issue} :
    let area := layout site.destination.width element
    let child := canonicalCollectionTail site.destination site.inst entries area route.output pointer
      (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply
    let reply := route.reply site.destination site.start.host.nextTicket
      (.error (LinkedCallback.CollectionVisit.afterAllocation index issue))
    CollectionRangeCut profile ready base bindings older checked canonical check site.destination area entries.length pointer
      (Field.listObjects entries)
      (fun addr live => checkedCollectionTail site.destination site.inst entries area index route.output addr live >>= site.reply)
      (fun addr => canonicalCollectionTail site.destination site.inst entries area route.output addr
        (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply) →
    Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) leading checked (.active 0 1) →
    (core3 grow).memSize? checked.store.core site.destination.memory = some bytes →
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    Stored.OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
    ∃ (canon : Cursor (E := core3 grow) (HostState sig)) (checkedLabels canonLabels : Trace grow sig)
      (segments : List (Seg (core3 grow) (HostState sig))),
      (∀ label ∈ checkedLabels, label = .tau) ∧ (∀ label ∈ canonLabels, label = .tau) ∧
      Steps profile ready (specDispatch ready base) checked (checkedLabels ++ [.tau, .tau, .tau])
        { checked with
          host := checked.host.record reply.1
          ctl := ⟨check.thread, .core ((core3 grow).resume checked.store.core site.core (.values reply.2)) site.resume,
            segments⟩ :: check.rest } ∧
      RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonLabels
        { canonical with ctl := canon.control child } := by
  intro area child reply cut caller sized aligned bounds refused
  obtain ⟨canon, capacity, _, atCapacity, _, reached⟩ := cut
  have sameCapacity := Option.some.inj (atCapacity.symm.trans sized)
  subst capacity
  simp only [ite_eq_right (not_not_intro aligned), ite_eq_left bounds] at reached
  obtain ⟨⟨lhs, checkTau, checkedRun⟩, ⟨rhs, canonTau, canonRun⟩⟩ := reached
  rw [refused] at checkedRun
  let stopped := site.reply (.error (LinkedCallback.CollectionVisit.afterAllocation index issue))
  have stop : (checkedCollectionTail site.destination site.inst entries area index route.output pointer (.error issue) >>= site.reply) =
      stopped := by cases issue <;> rfl
  rw [stop] at checkedRun
  let reached := { checked with ctl := check.control stopped }
  obtain ⟨segments, atCaller⟩ := site.reached_caller (reached := reached) (body := stopped) rfl (caller.append (checkedRun 0))
  have atReply : reached.ctl = ⟨check.thread, .prog (do return .flat (← writeCompletion reply)),
        .core site.core site.resume :: segments⟩ :: check.rest := by
    simp only [reached, Cursor.control, atCaller, stopped, PayloadRoot.Site.reply, reply]
  exact ⟨canon, lhs, rhs, segments, checkTau, canonTau,
    appendRun (prefix_survives (checkedRun 0)).1 (Plain.give_completion_steps reply atReply), canonRun⟩

private theorem collectionCaller {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (type element : Stored.TypeOf) (entries : List Field)
    (field : site.field = .dynamic type element entries)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.checked.store site.checked.host.writer (Field.listObjects entries) = .ok ())
    {checked : Config (core3 grow) (HostState sig)} {checkTrace} :
    let area := layout site.destination.width element
    let resume := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    Trail profile ready (specDispatch ready base)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor resume)
      (some (.active 0 0)) checkTrace checked (some (.active 0 0)) →
    ∃ trace, Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) trace checked (.active 0 1) := by
  intro area resume trail
  have width := site.destination.check_width site.start.store linked.destination
  have checkAt : site.checked.ctl = site.cursor.control (Stored.OwnedMemory.Claims.Record.Effects.field
      recordClaims Limits.spec Quirks.none (site.destination.context site.inst) site.destination.width
      (.dynamic type element entries) 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  have canonAt := site.reference_at linked site.referenceReply
  rw [field] at canonAt
  have entered := (collection_install_tracks (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    site.destination site.inst type element entries route.output 0 site.checked (site.reference site.referenceReply)
    site.cursor site.cursor site.reply site.referenceReply width prepared checkAt canonAt 0).1
  obtain ⟨place, initial, track⟩ := trail.survives
  cases initial
  exact ⟨_, entered.append (track.under 1)⟩

theorem localListReplies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (data : LocalDataType element)
    (field : site.field = .dynamic (.list element) element entries) (pointer : Nat)
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width element
    let first := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionReplies profile ready base bindings older site checked canonical
      (canonicalCollectionTail site.destination site.inst entries area route.output pointer >>= site.referenceReply) := by
  intro area first second mark paired returned growth
  obtain ⟨objects, compiled⟩ := linked.compiled
  have matched := Stored.OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ objects compiled
  rw [field] at matched
  have children := listEntries matched
  have width := site.destination.check_width site.start.store linked.destination
  have prepared : Stored.OwnedMemory.Claims.Record.prepare site.checked.store site.checked.host.writer
      (Field.listObjects entries) = .ok () := by rw [local_data_objects data children]; rfl
  obtain ⟨_, caller⟩ := collectionCaller site linked (.list element) element entries field prepared mark.checkedTrail
  have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.list element) element
    entries route.output 0 pointer site.reply site.referenceReply mark paired returned width growth
  exact replies site caller (localTail site.destination site.inst element entries .value route.output 0 pointer
    site.reply site.referenceReply (fun bytes left right canon reachedWidth sized aligned bounds same thread checkAt rightAt =>
      local_data_collection_tail site.destination site.inst element data entries children pointer bytes 0 route.output left right
        reachedWidth sized aligned bounds same check canon thread site.reply site.referenceReply checkAt rightAt) cut)

theorem nominalListReplies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element) (field : site.field = .dynamic (.list element) element entries) (pointer : Nat)
    (admitted : Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width element
    let first := checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionSegmentReplies profile ready base bindings older site checked canonical
      (ListReturnStop site.destination site.inst entries area route.output pointer site.referenceReply) := by
  intro area first second mark paired returned growth
  obtain ⟨objects, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ objects compiled
  have emitted := Record.preflightValue_emitted _ _ _ _ _ objects compiled
  rw [field] at matched emitted admitted
  have entriesMatch := listEntries matched
  cases emitted with
  | list children =>
    have handles : ∀ item ∈ entries, CanonicalHandle item := fun item member =>
      nominalEntry nominal (entries_match_of_mem entriesMatch member) (children item member)
    obtain ⟨_, caller⟩ := collectionCaller site linked (.list element) element entries field admitted mark.checkedTrail
    have width := site.destination.check_width site.start.store linked.destination
    have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.list element) element
      entries route.output 0 pointer site.reply site.referenceReply mark paired returned width growth
    refine replies site caller (rangeThen site.destination site.inst element entries .value route.output 0 pointer
      site.reply site.referenceReply (ListReturnStop site.destination site.inst entries area route.output pointer site.referenceReply)
      (.inl rfl) ?_ cut)
    intro _ left right canon _ _ _ _ frame checkAt canonAt
    obtain ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, leftRun, rightRun, same, seen, status⟩ :=
      finishElements site.destination site.inst entries area .value route.output 0 pointer site.reply site.referenceReply checkAt canonAt
        (ElementStop site.destination site.inst entries area.size pointer)
        (fun checkTail canonTail lhs rhs => nominalElements site.destination site.inst entries handles area.size pointer 0
          checkTail canonTail frame lhs rhs)
    refine ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, leftRun, rightRun, same, seen, ?_⟩
    cases outcome with
    | returned _ | trapped _ => exact status
    | refused _ =>
      obtain ⟨stop, witness, rest⟩ := status
      exact ⟨stop, .inr witness, rest⟩

private theorem nominalMapElements (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output)
    (keyData : LocalDataType (.prim key.toPrimitive)) (nominal : NominalElement element)
    (origin : CStore (core3 grow)) (basePtr bytes count : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entries : List Field) (index : Nat) (room : index + entries.length ≤ count)
    (shape : ∀ item ∈ entries, ∃ (keyPayload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      item = .aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) keyPayload, value] ∧
        value.LayoutMatches element ∧ value.Emitted)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core) :
    let stride := (layout destination.width (.record (mapEntryFields key element))).size
    let ptr := basePtr + index * stride
    let cx := destination.context inst
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width entries stride ptr index >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries
      mode stride ptr >>= canonNext) →
    CollectionSegment profile ready base bindings older left right check checkNext canonNext 0
      (MapValueStop destination inst key element mode entries stride ptr canonNext) := by
  induction entries generalizing index left right check canon with
  | nil =>
    intro _ _ _ _ checkAt canonAt
    simp only [Record.Effects.elements, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] at checkAt canonAt
    exact ⟨canon, .returned (), [], [], left, right, .refl _, .refl _, frame.store, rfl,
      frame, checkAt, canonAt, fun depth => .done _ _, fun depth => .done _ _, trivial⟩
  | cons item rest ih =>
    intro stride ptr cx mode checkAt canonAt
    have valid : index < count := by simp only [List.length_cons] at room; omega
    have nextRoom : index + 1 + rest.length ≤ count := by simp only [List.length_cons] at room; omega
    have nextPtr : basePtr + (index + 1) * stride = ptr + stride := by
      simp only [ptr, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    obtain ⟨keyPayload, value, shapeHead, matched, emitted⟩ := shape item (by simp)
    let type : Stored.TypeOf := .record (mapEntryFields key element)
    let keyField := Field.data (.prim key.toPrimitive) keyPayload
    let checkTail : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)) := fun verdict =>
      (match verdict with
        | .error issue => pure (.error issue)
        | .ok () => Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width rest stride (ptr + stride) (index + 1))
        >>= checkNext
    let canonRest : Session grow sig Unit := CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest mode stride (ptr + stride)
    let canonTail : Unit → Session grow sig (Ret (core3 grow)) := fun _ => canonRest >>= canonNext
    let afterKey := fun (keyWidth : AddrType) (_ : Unit) => mapFieldPlacement cx mode fun reached =>
      let area := layout keyWidth keyField.type
      let address := alignTo (alignTo ptr area.alignment + area.size) (layout reached value.type).alignment
      CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory address) >>= canonTail
    have atHead : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
        (.aggregate type [keyField, value]) index (.memory ptr) >>= checkTail) := by
      rw [checkAt, shapeHead, Record.Effects.elements]
      congr 1
      simp only [Prog.bind_eq, Prog.bind_assoc, checkTail]
      congr 1
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok result => cases result; rfl
    have atCanonHead : right.ctl = canon.control (mapFieldPlacement cx mode fun reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField
          (.memory (alignTo ptr (layout reached keyField.type).alignment)) >>= afterKey reached) := by
      rw [canonAt, shapeHead]
      apply congrArg canon.control
      let readWidth : Session grow sig AddrType := ptrType cx
      let keySlot := fun reached => alignTo ptr (layout reached keyField.type).alignment
      let keyBody : AddrType → Session grow sig Unit := fun reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField (.memory (keySlot reached))
      let valBody : AddrType → AddrType → Session grow sig Unit := fun keyWidth reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width value
          (.memory (alignTo (keySlot keyWidth + (layout keyWidth keyField.type).size) (layout reached value.type).alignment))
      cases output with
      | memory address =>
        let reached := destination.width
        change ((keyBody reached).bind (fun _ => (valBody reached reached).bind (fun _ => canonRest))).bind canonNext =
          (keyBody reached).bind (fun _ => (valBody reached reached).bind (fun _ => canonRest.bind canonNext))
        simp only [Prog.bind_assoc]
      | flat =>
        change ((readWidth.bind (fun keyWidth => (keyBody keyWidth).bind fun _ =>
          readWidth.bind fun reached => (valBody keyWidth reached).bind fun _ => .pure ())).bind (fun _ => canonRest)).bind canonNext =
          readWidth.bind (fun keyWidth => (keyBody keyWidth).bind fun _ =>
            readWidth.bind fun reached => (valBody keyWidth reached).bind fun _ => canonRest.bind canonNext)
        simp only [Prog.bind_assoc, Prog.pure_bind']
    obtain ⟨reached, outcome, headLeft, headRight, middleLeft, middleRight, runHeadLeft, runHeadRight, same, seen, status⟩ :=
      nominalMapEntry (profile := profile) (ready := ready) (base := base) (bindings := bindings)
        destination inst key element output keyData keyPayload value nominal matched emitted origin basePtr bytes count index width sized aligned bounds
        valid index checkTail canonTail frame growth atHead atCanonHead
    cases outcome with
    | trapped reason => exact ⟨reached, .trapped reason, _, _, _, _, runHeadLeft, runHeadRight, same, seen, status⟩
    | refused issue =>
      obtain ⟨stop, stopped, leftAt, rightAt, leftTracks, rightTracks⟩ := status
      refine ⟨reached, .refused issue, _, _, _, _, runHeadLeft, runHeadRight, same, seen, stop,
        ⟨[], rest, keyField, value, congrArg (· :: rest) shapeHead, ?_⟩, leftAt, rightAt, leftTracks, rightTracks⟩
      change stop = mapValueSuffix destination inst mode keyField value rest stride (ptr + 0 * stride) canonNext
      rw [Nat.zero_mul, Nat.add_zero]
      exact stopped
    | returned result =>
      cases result
      obtain ⟨paired, reachedLeft, reachedRight, leftTracks, rightTracks, grown⟩ := status
      have next := ih (index + 1) nextRoom (fun child member => shape child (List.mem_cons_of_mem _ member))
        paired (paired.store ▸ grown)
      dsimp only at next
      have advance : basePtr + (index + 1) * (layout destination.width (.record (mapEntryFields key element))).size = ptr + stride := nextPtr
      rw [advance] at next
      obtain ⟨last, outcome, tailLeft, tailRight, finalLeft, finalRight, runTailLeft, runTailRight, sameFinal, seenTail, finish⟩ :=
        next reachedLeft reachedRight
      refine ⟨last, outcome, _, _, finalLeft, finalRight, appendRun runHeadLeft runTailLeft, appendRun runHeadRight runTailRight,
        sameFinal, by rw [appendVisible, appendVisible, seen, seenTail], ?_⟩
      cases outcome with
      | returned result =>
        obtain ⟨finalPair, leftAt, rightAt, leftTail, rightTail, kept⟩ := finish
        exact ⟨finalPair, leftAt, rightAt, fun depth => (leftTracks depth).append (leftTail depth),
          fun depth => (rightTracks depth).append (rightTail depth), kept⟩
      | refused issue =>
        obtain ⟨stop, ⟨leading, suffix, keySlot, valueSlot, split, stopped⟩, leftAt, rightAt, leftTail, rightTail⟩ := finish
        refine ⟨stop, ⟨item :: leading, suffix, keySlot, valueSlot, congrArg (item :: ·) split, ?_⟩,
          leftAt, rightAt, fun depth => (leftTracks depth).append (leftTail depth), fun depth => (rightTracks depth).append (rightTail depth)⟩
        have address : ptr + (item :: leading).length * stride = (ptr + stride) + leading.length * stride := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
        change stop = mapValueSuffix destination inst mode keySlot valueSlot suffix stride
          (ptr + (item :: leading).length * stride) canonNext
        rw [address]
        exact stopped
      | trapped reason =>
        obtain ⟨leftDone, rightDone, leading, stopped⟩ := finish
        exact ⟨leftDone, rightDone, visible headRight ++ leading, by rw [appendVisible, stopped, List.append_assoc]⟩

private theorem mapEntries {entries : List Field} {key : WIT.KeyType} {element schema : Stored.TypeOf}
    (matched : Field.LayoutMatches (.dynamic (.map key element) (.record (mapEntryFields key element)) entries) schema) :
    Field.EntriesMatch entries (.record (mapEntryFields key element)) := by
  cases matched with
  | map children => exact children

private theorem mapValueLayout {key : WIT.KeyType} {element : Stored.TypeOf} {keyField value : Field}
    (matched : Field.LayoutMatches (.aggregate (.record (mapEntryFields key element)) [keyField, value])
      (.record (mapEntryFields key element))) : value.LayoutMatches element := by
  cases matched with
  | record fields =>
    cases fields with
    | cons _ tail =>
      cases tail with
      | cons shape _ => exact shape

private theorem liveMapEntry (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (keyData : LocalDataType (.prim key.toPrimitive))
    (keyPayload : Stored.Payload (.prim key.toPrimitive)) (value : Field) (origin : CStore (core3 grow))
    (basePtr bytes count idx : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entry : idx < count) (compare : FieldComparison grow sig)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (done : ∀ lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext (.ok ())) →
      rhs.ctl = canon.control (canonNext ()) → finish lhs rhs check canon) :
    let type : Stored.TypeOf := .record (mapEntryFields key element)
    let ptr := basePtr + idx * (layout destination.width type).size
    let keyField := Field.data (.prim key.toPrimitive) keyPayload
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    let cx := destination.context inst
    value.type = element → (∀ address, PlacedFieldRule compare older origin destination inst value address) →
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [keyField, value]) idx (.memory ptr) >>= checkNext) →
    right.ctl = canon.control (mapFieldPlacement cx mode (mapKeyBody destination inst ptr mode keyField value canonNext)) →
    LiveMapEntryThen profile ready base bindings destination inst mode keyField value idx ptr compare checkNext canonNext finish
      left right check canon := by
  intro type ptr keyField mode cx valueType rule checkAt canonAt
  let keyArea := layout destination.width keyField.type
  let afterKey := alignTo ptr keyArea.alignment + keyArea.size
  let address := alignTo afterKey (layout destination.width value.type).alignment
  let report := aggregateNext idx checkNext
  let pending := fun () => mapValueProgram destination inst mode value afterKey canonNext
  let atKey := { right with ctl := canon.control (mapKeyBody destination inst ptr mode keyField value canonNext destination.width) }
  obtain ⟨keyRead, quiet, tracks⟩ := mapPlacement (profile := profile) (ready := ready) (base := base) (bindings := bindings)
    destination inst key element output right canon _ (growth.memAddrType width) canonAt
  obtain ⟨store, result, lhs, rhs, checkRun, canonRun, observed, keyResult⟩ :=
    local_map_key_then_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst key element keyData keyPayload value
      origin basePtr bytes count idx width sized aligned bounds entry idx left atKey growth frame.store
      check canon frame.thread checkNext pending checkAt rfl
  refine ⟨keyRead, quiet, tracks, store, result, lhs, rhs, checkRun, canonRun, observed, ?_⟩
  cases result with
  | error reason => exact keyResult
  | ok data =>
    cases data
    obtain ⟨grown, checked, canonical⟩ := keyResult
    let beforeValue := { right with store, ctl := canon.control (pending ()) }
    let valueBody := fun reached => CanonicalTree.field Limits.spec Quirks.none cx destination.width value
      (.memory (alignTo afterKey (layout reached value.type).alignment)) >>= canonNext
    obtain ⟨valueRead, silent, valueTracks⟩ := mapPlacement (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst key element output beforeValue canon valueBody (grown.memAddrType width) rfl
    refine ⟨checked, canonical, valueRead, silent, valueTracks, ?_⟩
    apply rule address 1 report canonNext
    · exact ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    · exact grown
    · exact grown.memAddrType width
    · simp only [address, valueType]
      exact (map_entry_placement destination inst key element grown width sized aligned bounds entry).2.2
    · rfl
    · rfl
    · exact done

private def MapSlotRule (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (origin : CStore (core3 grow))
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field) (idx ptr : Nat)
    (compare : FieldComparison grow sig) (entry : MapEntryComparison grow sig) : Prop :=
  let cx := destination.context inst
  let keyField := Field.data (.prim key.toPrimitive) payload
  let type : Stored.TypeOf := .record (mapEntryFields key element)
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
  ∀ (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)},
    LinkedCallback.ChildFrameOver older left right check canon → Core3.Grows origin.core right.store.core →
    (∀ address, PlacedFieldRule compare older origin destination inst value address) →
    (∀ lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext (.ok ())) →
      rhs.ctl = canon.control (canonNext ()) → finish lhs rhs check canon) →
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [keyField, value]) idx (.memory ptr) >>= checkNext) →
    right.ctl = canon.control (mapFieldPlacement cx mode (mapKeyBody destination inst ptr mode keyField value canonNext)) →
    entry keyField value idx ptr compare checkNext canonNext finish left right check canon

private theorem liveMapElementsRule (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (entryRule : MapEntryComparison grow sig)
    (origin : CStore (core3 grow)) (basePtr count : Nat)
    (entries : List Field) (idx : Nat) (room : idx + entries.length ≤ count) (compare : FieldComparison grow sig)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (keyAllowed : Stored.Payload (.prim key.toPrimitive) → Field → Prop)
    (solve : ∀ payload value, keyAllowed payload value → ∀ idx, idx < count →
      MapSlotRule destination inst key element output origin older payload value idx
        (basePtr + idx * (layout destination.width (.record (mapEntryFields key element))).size) compare entryRule)
    (shape : ∀ item ∈ entries, ∃ (keyPayload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      item = .aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) keyPayload, value] ∧
        keyAllowed keyPayload value ∧ ∀ address, PlacedFieldRule compare older origin destination inst value address)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    (done : ∀ lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext (.ok ())) →
      rhs.ctl = canon.control (canonNext ()) → finish lhs rhs check canon)
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core) :
    let stride := (layout destination.width (.record (mapEntryFields key element))).size
    let ptr := basePtr + idx * stride
    let cx := destination.context inst
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
    left.ctl = check.control (Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width entries stride ptr idx >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries mode stride ptr >>= canonNext) →
    liveMapElementsWith entryRule destination inst key element output compare checkNext canonNext finish entries idx ptr
      left right check canon := by
  induction entries generalizing idx left right check canon with
  | nil => intro _ _ _ _ checkAt canonAt; exact done left right check canon frame growth checkAt canonAt
  | cons item rest ih =>
    intro stride ptr cx mode checkAt canonAt
    have valid : idx < count := by simp only [List.length_cons] at room; omega
    have nextRoom : idx + 1 + rest.length ≤ count := by simp only [List.length_cons] at room; omega
    have nextPtr : basePtr + (idx + 1) * stride = ptr + stride := by
      simp only [ptr, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    obtain ⟨keyPayload, value, entry, allowed, rule⟩ := shape item (by simp)
    let type : Stored.TypeOf := .record (mapEntryFields key element)
    let keyField := Field.data (.prim key.toPrimitive) keyPayload
    let checked := checkTail (.elements stride) destination inst rest (idx + 1) (ptr + stride) checkNext
    let canonRest : Session grow sig Unit := CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest mode stride (ptr + stride)
    let canonical : CanonNext grow sig := fun () => canonRest >>= canonNext
    have atHead : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
        (.aggregate type [keyField, value]) idx (.memory ptr) >>= checked) := by
      rw [checkAt, entry, Record.Effects.elements]
      congr 1
      simp only [Prog.bind_eq, Prog.bind_assoc, checked]
      congr 1
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok result => cases result; rfl
    have atCanonHead : right.ctl = canon.control (mapFieldPlacement cx mode (mapKeyBody destination inst ptr mode keyField value canonical)) := by
      rw [canonAt, entry]
      apply congrArg canon.control
      let readWidth : Session grow sig AddrType := ptrType cx
      let keySlot := fun reached => alignTo ptr (layout reached keyField.type).alignment
      let keyBody : AddrType → Session grow sig Unit := fun reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField (.memory (keySlot reached))
      let valueBody : AddrType → AddrType → Session grow sig Unit := fun keyWidth reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width value
          (.memory (alignTo (keySlot keyWidth + (layout keyWidth keyField.type).size) (layout reached value.type).alignment))
      cases output with
      | memory address =>
        simp only [mode, CanonicalTree.EntryMode.forOutput, CanonicalTree.elements]
        let reached := destination.width
        change ((keyBody reached).bind (fun _ => (valueBody reached reached).bind (fun _ => canonRest))).bind canonNext =
          (keyBody reached).bind (fun _ => (valueBody reached reached).bind canonical)
        simp only [canonical, Prog.bind_eq, Prog.bind_assoc]
      | flat =>
        simp only [mode, CanonicalTree.EntryMode.forOutput, CanonicalTree.elements]
        change ((readWidth.bind (fun keyWidth => (keyBody keyWidth).bind fun _ =>
          readWidth.bind fun reached => (valueBody keyWidth reached).bind fun _ => .pure ())).bind (fun _ => canonRest)).bind canonNext =
          readWidth.bind (fun keyWidth => (keyBody keyWidth).bind fun _ =>
            readWidth.bind fun reached => (valueBody keyWidth reached).bind canonical)
        simp only [canonical, Prog.bind_eq, Prog.bind_assoc, Prog.pure_bind']
    refine ⟨keyPayload, value, entry, solve keyPayload value allowed idx valid checked canonical _
      frame (frame.store ▸ growth) rule ?_ atHead atCanonHead⟩
    intro lhs rhs check canon paired kept checkAt canonAt
    have tail := ih (idx + 1) nextRoom (fun child member => shape child (.tail _ member)) paired kept
    dsimp only at tail
    rw [nextPtr] at tail
    exact tail checkAt canonAt

private def MapEntryResolver (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (count : Nat) (output : Stored.Lower.Output) (compare : FieldComparison grow sig)
    (entry : MapEntryComparison grow sig) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (keyAllowed : Stored.Payload (.prim key.toPrimitive) → Field → Prop) : Prop :=
  let area := layout destination.width (.record (mapEntryFields key element))
  ∀ (origin : CStore (core3 grow)) (pointer bytes : Nat),
    (core3 grow).memAddrType? origin.core destination.memory = some destination.width →
    (core3 grow).memSize? origin.core destination.memory = some bytes →
    pointer = alignTo pointer area.alignment → pointer + count * area.size ≤ bytes →
    ∀ payload value, keyAllowed payload value → ∀ idx, idx < count →
      MapSlotRule destination inst key element output origin older payload value idx (pointer + idx * area.size) compare entry

private theorem liveMapVisitorWith (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output) (compare : FieldComparison grow sig)
    (entry : MapEntryComparison grow sig) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow))
    (keyAllowed : Stored.Payload (.prim key.toPrimitive) → Field → Prop)
    (solve : MapEntryResolver destination inst key element entries.length output compare entry older keyAllowed)
    (shape : ∀ item ∈ entries, ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      item = .aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) payload, value] ∧
        keyAllowed payload value ∧ ∀ (reached : CStore (core3 grow)) address, PlacedFieldRule compare older reached destination inst value address)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (finish : ValueFinish grow sig output)
    (done : ∀ value lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext (.ok value)) →
      rhs.ctl = canon.control (canonNext value) → finish value lhs rhs check canon) :
    CollectionVisitor destination inst (.map key element) (.record (mapEntryFields key element)) entries index output
      checkNext canonNext older origin
      (liveMapTailWith profile ready base bindings entry destination inst key element entries index output compare checkNext canonNext finish) := by
  intro pointer bytes lhs rhs check canon frame grown width sized aligned bounds checkAt canonAt
  let area := layout destination.width (.record (mapEntryFields key element))
  let mode := CanonicalTree.EntryMode.forOutput destination.width (.map key element) output
  let checked := publishChecked destination inst pointer entries.length index output checkNext
  let canonical := publishCanonical destination inst pointer entries.length output canonNext
  obtain ⟨checkElements, canonElements⟩ := collectionElementFoci destination inst entries area mode output pointer index
    checkNext canonNext checkAt canonAt
  have visits : ∀ item ∈ entries, ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      item = .aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) payload, value] ∧
        keyAllowed payload value ∧ ∀ address, PlacedFieldRule compare older lhs.store destination inst value address := by
    intro item member
    obtain ⟨payload, value, shape, allowed, compareAt⟩ := shape item member
    exact ⟨payload, value, shape, allowed, compareAt lhs.store⟩
  have publish := fun left right cursor peer paired kept leftAt rightAt =>
    livePublish (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst pointer entries.length output checkNext canonNext finish done
      (left := left) (right := right) (check := cursor) (canon := peer) paired (grown.trans kept) leftAt rightAt
  simpa only [liveMapTailWith, Nat.zero_mul, Nat.add_zero] using
    liveMapElementsRule destination inst key element output entry lhs.store pointer entries.length entries 0 (Nat.zero_add _).le
      compare keyAllowed (solve lhs.store pointer bytes width sized aligned bounds) visits checked canonical
      (LiveListPublish profile ready base bindings output checkNext canonNext finish) publish frame (Core3.Grows.refl _)
      (by simpa only [Nat.zero_mul, Nat.add_zero] using checkElements)
      (by simpa only [Nat.zero_mul, Nat.add_zero] using canonElements)

private theorem liveMapVisitor (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : Stored.TypeOf)
    (entries : List Field) (index : Nat) (output : Stored.Lower.Output) (compare : FieldComparison grow sig)
    (keyData : LocalDataType (.prim key.toPrimitive)) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow))
    (shape : ∀ item ∈ entries, ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      item = .aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) payload, value] ∧
        value.type = element ∧ ∀ (reached : CStore (core3 grow)) address, FieldRule compare older reached destination inst value address)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (finish : ValueFinish grow sig output)
    (done : ∀ value lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext (.ok value)) →
      rhs.ctl = canon.control (canonNext value) → finish value lhs rhs check canon) :
    CollectionVisitor destination inst (.map key element) (.record (mapEntryFields key element)) entries index output
      checkNext canonNext older origin
      (liveMapTail profile ready base bindings destination inst key element entries index output compare checkNext canonNext finish) := by
  refine liveMapVisitorWith destination inst key element entries index output compare _ older origin (fun _ value => value.type = element)
    ?_ ?_ checkNext canonNext finish done
  · intro reached pointer bytes width sized aligned bounds payload value valueType idx valid
      checked canonical last left right check canon frame growth rule doneAt checkAt canonAt
    exact liveMapEntry destination inst key element output keyData payload value reached pointer bytes entries.length idx
      width sized aligned bounds valid compare checked canonical last frame growth doneAt valueType rule checkAt canonAt
  · intro item member
    obtain ⟨payload, value, entry, valueType, child⟩ := shape item member
    exact ⟨payload, value, entry, valueType, fun reached address => placedFieldOfRule (child reached address)⟩

private theorem mapCompiled {item : Field} {key : WIT.KeyType} {element : Stored.TypeOf}
    (matched : item.LayoutMatches (.map key element)) (emitted : item.Emitted) :
    ∃ entries, item = .dynamic (.map key element) (.record (mapEntryFields key element)) entries ∧
      ∀ entry ∈ entries, ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
        entry = .aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) payload, value] ∧
          value.LayoutMatches element ∧ value.Emitted := by
  cases emitted with
  | map entries emitted =>
    cases matched with
    | map layouts =>
      refine ⟨_, rfl, ?_⟩
      intro entry member
      obtain ⟨payload, value, shape⟩ := entries entry member
      have layout := entries_match_of_mem layouts member
      rw [shape] at layout member
      exact ⟨payload, value, shape, mapValueLayout layout, emitted payload value member⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | primitive | enum | flags | context | owner | aggregate | fixed | list | sum => cases matched

private theorem preflightAllocator {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) : Field.AllocatorFor site.destination.realloc site.field := by
  intro child desc pointer
  obtain ⟨plan, compiled⟩ := linked.compiled
  have rootPtr := desc.containsPtr (Record.preflightValue_layout _ _ _ _ _ plan compiled) pointer
  cases alloc : site.destination.realloc with
  | some addr => exact ⟨addr, rfl⟩
  | none =>
    have options : Stored.Lower.checkOptions (site.destination.context (grow := grow) site.inst) (sig.payload site.tag)
        route.output = .error .reallocRequired := by
      simp [Stored.Lower.checkOptions, RecordDestination.context, rootPtr, alloc, Option.isNone]
      rfl
    simp only [Record.preflightValue, bind, Except.bind, Except.mapError] at compiled
    split at compiled
    · contradiction
    · simp [RecordLower.compileValue, options, bind, Except.bind, Except.mapError] at compiled

private theorem mapStringKeyFinish (destination : RecordDestination) (inst : InstId) (key : LinkedCallback.StringField)
    (address : Nat) (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {first second : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop}
    (next : ∀ pointer lhs rhs cursor peer, first pointer lhs rhs cursor peer → second pointer lhs rhs cursor peer)
    (replay : StringKeyThen profile ready base bindings older destination inst key address left right check canon checkNext canonNext first) :
    StringKeyThen profile ready base bindings older destination inst key address left right check canon checkNext canonNext second := by
  obtain ⟨lhs, rhs, checkSeen, canonSeen, checkTracks, canonTracks, frame, rest⟩ := replay
  exact ⟨lhs, rhs, checkSeen, canonSeen, checkTracks, canonTracks, frame, CallbackPrefix.stringReplayMap next rest⟩

private theorem stringMapSlotRule (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (root : Field) {schema : Stored.TypeOf}
    (layoutRoot : root.LayoutMatches schema)
    (fitRoot : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocator : Field.AllocatorFor destination.realloc root)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (origin : CStore (core3 grow)) (pointer bytes count : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : pointer = alignTo pointer (layout destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : pointer + count * (layout destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (payload : Stored.Payload (.prim .string)) (value : Field)
    (valueType : value.type = element)
    (path : Field.Descendant root (.aggregate (.record (mapEntryFields .string element)) [.data (.prim .string) payload, value]))
    (idx : Nat) (valid : idx < count) (compare : FieldComparison grow sig)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    MapSlotRule destination inst .string element output origin older payload value idx
      (pointer + idx * (layout destination.width (.record (mapEntryFields .string element))).size) compare
      (LiveStringMapEntryThen profile ready base bindings older destination inst element output) := by
  obtain ⟨str, typed⟩ := payload
  cases typed with
  | int kind _ => cases kind
  | string validString =>
    intro checkNext canonNext finish left right check canon frame growth rule done checkAt canonAt
    let cx : LiftLowerContext (core3 grow) := destination.context inst
    let type : Stored.TypeOf := .record (mapEntryFields .string element)
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
    let key : LinkedCallback.StringField := ⟨_, validString⟩
    let area := layout destination.width key.field.type
    let keyPtr := alignTo (pointer + idx * (layout destination.width type).size) area.alignment
    let keyEnd := keyPtr + area.size
    let valuePtr := alignTo keyEnd (layout destination.width value.type).alignment
    let pending := fun () => mapValueProgram destination inst mode value keyEnd canonNext
    have keyRun := stringMapKey (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst element output key value root layoutRoot fitRoot allocator path origin pointer bytes count idx idx
      width sized aligned bounds valid checkNext canonNext frame growth embedder checkAt canonAt
    refine ⟨key, rfl, mapStringKeyFinish _ _ _ _ _ _ ?_ keyRun⟩
    intro address lhs rhs cursor peer reached
    obtain ⟨related, kept, store, result, labels, observed, checkRun, canonRun, tracks⟩ := reached
    refine ⟨store, result, labels, observed, checkRun, canonRun, ?_⟩
    cases result with
    | error reason => exact True.intro
    | ok valueDone =>
      cases valueDone
      let beforeValue := { rhs with store, ctl := peer.control (pending ()) }
      let valueBody := fun reached => CanonicalTree.field Limits.spec Quirks.none cx destination.width value
        (.memory (alignTo keyEnd (layout reached value.type).alignment)) >>= canonNext
      have grew := kept.trans checkRun.grows
      obtain ⟨widthRead, silent, placed⟩ := mapPlacement (profile := profile) (ready := ready) (base := base)
        (bindings := bindings) destination inst .string element output beforeValue peer valueBody (grew.memAddrType width) rfl
      refine ⟨fun depth => (tracks () rfl depth).1, fun depth => (tracks () rfl depth).2, widthRead, silent, placed, ?_⟩
      apply rule valuePtr 1 (aggregateNext idx checkNext) canonNext
      · exact ⟨rfl, related.pending, related.results, related.cancels, related.blocked, related.thread, related.frames, related.rest⟩
      · exact grew
      · exact grew.memAddrType width
      · simp only [valuePtr, valueType]
        exact (map_entry_placement destination inst .string element grew width sized aligned bounds valid).2.2
      · rfl
      · rfl
      · exact done

private structure CollectionSource (destination : RecordDestination) (root : Field) (schema : Stored.TypeOf) : Prop where
  layout : root.LayoutMatches schema
  fits : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true
  allocator : Field.AllocatorFor destination.realloc root

private theorem dataCompiled {type : Stored.TypeOf} {item : Field} (data : LocalDataType type)
    (matched : item.LayoutMatches type) : ∃ payload : Stored.Payload type, item = .data type payload := by
  cases matched with
  | data payload => exact ⟨payload, rfl⟩
  | @endpoint channel _ _ => cases channel <;> cases data
  | _ => cases data

private theorem localFieldThen (destination : RecordDestination) (inst : InstId) (type : Stored.TypeOf)
    (data : LocalDataType type) (payload : Stored.Payload type) (address : Nat)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)} :
    PlacedFieldRule (fun _ _ _ left right check canon checkNext canonNext finish =>
      LiveLocalFieldThen profile ready base bindings checkNext canonNext finish left right check canon)
      older origin destination inst (.data type payload) address := by
  intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
  obtain ⟨store, result, lhsTrace, rhsTrace, lhs, rhs, observed, cut⟩ :=
    local_data_leaf_frame_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst type data payload index
      (.memory address) origin left right (frame.store ▸ growth)
      (by simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, width]) placed
      frame.store check canon frame.thread checkNext canonNext checkAt canonAt
  refine ⟨store, result, lhsTrace, rhsTrace, lhs, rhs.steps, observed, ?_⟩
  cases result with
  | error reason => exact cut
  | ok val =>
    cases val
    obtain ⟨grew, checkTracks, canonTracks⟩ := cut
    exact ⟨checkTracks, canonTracks, ends _ _ check canon
      ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ grew rfl rfl⟩

private theorem stringCompiled {item : Field} (matched : item.LayoutMatches (.prim .string)) (emitted : item.Emitted) :
    ∃ str : LinkedCallback.StringField, item = str.field := by
  cases emitted with
  | primitive payload =>
    cases matched
    obtain ⟨val, typed⟩ := payload
    cases typed with
    | int kind _ => cases kind
    | string valid => exact ⟨⟨_, valid⟩, rfl⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | _ => cases matched

private theorem stringValueThen (destination : RecordDestination) (inst : InstId) (str : LinkedCallback.StringField)
    (output : Stored.Lower.Output) {root : Field} {rootSchema : Stored.TypeOf}
    (source : CollectionSource destination root rootSchema) (path : Field.Descendant root str.field)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    {index : Nat} {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (width : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width)
    (placed : rootPlacement destination left.store (.prim .string) output = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width str.field index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width str.field output >>= canonNext)) {finish : Nat → Finish grow sig}
    (ends : ∀ pointer lhs rhs cursor peer, LinkedCallback.ChildFrameOver older lhs rhs cursor peer →
      Core3.Grows origin.core lhs.store.core →
      let plan := storePlanFor Quirks.none destination.encoding destination.width str.value
      lhs.ctl = cursor.control (stringPlanTail (destination.context inst) destination.width output plan pointer >>= fun res => checkNext (.ok res)) →
      rhs.ctl = peer.control (stringPlanTail (destination.context inst) destination.width output plan pointer >>= canonNext) →
      finish pointer lhs rhs cursor peer) :
    StringValueThen profile ready base bindings older destination inst str output left right check canon checkNext canonNext finish := by
  let cx : LiftLowerContext (core3 grow) := destination.context inst
  let plan := storePlanFor Quirks.none destination.encoding destination.width str.value
  let payload : Stored.Payload (.prim .string) := ⟨.string str.value, .string str.valid⟩
  have fit := Field.Descendant.string_pre payload rfl path source.layout Quirks.none destination.encoding destination.width source.fits
  obtain ⟨alloc, realloc⟩ := source.allocator str.field path rfl
  obtain ⟨reads, lhs, rhs⟩ := string_plan_entry_between (profile := profile) (ready := ready)
    (dispatch := specDispatch ready base) (reference := specDispatch ready (LiveDispatch.host bindings base))
    destination inst str.value str.valid index output left right check canon checkNext canonNext frame.store
    (frame.store ▸ width) realloc fit placed checkAt canonAt
  let checked := fun pointer => stringPlanTail cx destination.width output plan pointer >>= fun res => checkNext (.ok res)
  let canonical := fun pointer => stringPlanTail cx destination.width output plan pointer >>= canonNext
  let checkBody := { left with ctl := check.control (runStoreSteps cx 0 plan.steps >>= checked) }
  let canonBody := { right with ctl := canon.control (runStoreSteps cx 0 plan.steps >>= canonical) }
  refine ⟨List.replicate reads .tau, [.tau], silent (fun _ member => List.eq_of_mem_replicate member),
    rfl, lhs, rhs, ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked,
      frame.thread, frame.frames, frame.rest⟩, ?_⟩
  refine CallbackPrefix.stringReplay (origin := origin) (left := checkBody) (right := canonBody) cx 0 plan.steps checked canonical
    ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    growth rfl rfl embedder ends

private theorem stringValueCommit (cx : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (plan : StorePlan) (pointer : Nat)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (checkAt : left.ctl = check.control (stringPlanTail cx width output plan pointer >>= fun value => checkNext (.ok value)))
    (canonAt : right.ctl = canon.control (stringPlanTail cx width output plan pointer >>= canonNext)) :
    LiveValueCommit profile ready base bindings output checkNext canonNext (fun _ => LinkedCallback.ChildFrameOver older)
      left right check canon := by
  obtain ⟨store, outcome, labels, seen, checked, reference, tracks⟩ := string_descriptor_cut_between
    (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    (reference := specDispatch ready (LiveDispatch.host bindings base)) cx width output plan pointer left right check canon
    (fun value => checkNext (.ok value)) canonNext frame.store checkAt canonAt
  refine ⟨store, outcome, labels, seen, checked, reference, ?_⟩
  intro value equal
  subst outcome
  exact ⟨fun depth => (tracks value rfl depth).1, fun depth => (tracks value rfl depth).2,
    ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩⟩

private theorem stringFieldThen (destination : RecordDestination) (inst : InstId) (str : LinkedCallback.StringField)
    (address : Nat) {root : Field} {rootSchema : Stored.TypeOf}
    (source : CollectionSource destination root rootSchema) (path : Field.Descendant root str.field)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)} :
    PlacedFieldRule (liveCollectionField profile ready base bindings older destination inst (.prim .string))
      older origin destination inst str.field address := by
  intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
  let cx : LiftLowerContext (core3 grow) := destination.context inst
  let output := Stored.Lower.Output.memory address
  let plan := storePlanFor Quirks.none destination.encoding destination.width str.value
  refine ⟨str, rfl, stringValueThen destination inst str output source path embedder frame growth width placed checkAt canonAt ?_⟩
  intro pointer lhs rhs cursor peer paired grew _ checkAt canonAt
  obtain ⟨store, result, labels, observed, lhsRun, rhsRun, tracks⟩ :=
    string_descriptor_cut_between cx destination.width output plan pointer lhs rhs cursor peer
      (fun result => checkNext (.ok result)) canonNext paired.store checkAt canonAt
  refine ⟨store, result, labels, labels, lhsRun.steps, rhsRun.steps, rfl, ?_⟩
  cases result with
  | error reason => exact ⟨[], leafTrap observed⟩
  | ok val =>
    cases val
    exact ⟨fun depth => (tracks () rfl depth).1, fun depth => (tracks () rfl depth).2,
      ends _ _ cursor peer ⟨rfl, paired.pending, paired.results, paired.cancels, paired.blocked,
        paired.thread, paired.frames, paired.rest⟩ (grew.trans lhsRun.grows) rfl rfl⟩

private theorem liveCompiledMapVisitor (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType)
    (element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (compare : FieldComparison grow sig) (older : ReturnFrame.Substitutions (core3 grow) (HostState sig))
    (origin : CStore (core3 grow)) {root : Field} {schema : Stored.TypeOf}
    (source : CollectionSource destination root schema)
    (path : Field.Descendant root (.dynamic (.map key element) (.record (mapEntryFields key element)) entries))
    (shapes : ∀ item ∈ entries, ∃ (payload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
      item = .aggregate (.record (mapEntryFields key element)) [.data (.prim key.toPrimitive) payload, value] ∧
        value.LayoutMatches element ∧ value.Emitted)
    (child : ∀ value, Field.Descendant root value → value.LayoutMatches element → value.Emitted →
      ∀ reached address, PlacedFieldRule compare older reached destination inst value address)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (checkNext : ValueCheckNext grow sig output) (canonNext : ValueCanonNext grow sig output)
    (finish : ValueFinish grow sig output)
    (done : ∀ value lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext (.ok value)) →
      rhs.ctl = canon.control (canonNext value) → finish value lhs rhs check canon) :
    CollectionVisitor destination inst (.map key element) (.record (mapEntryFields key element)) entries index output
      checkNext canonNext older origin (liveMapTailWith profile ready base bindings
        (liveCollectionMapEntry profile ready base bindings older destination inst key element output)
        destination inst key element entries index output compare checkNext canonNext finish) := by
  refine liveMapVisitorWith destination inst key element entries index output compare _ older origin
    (fun payload value => value.type = element ∧ Field.Descendant root (.aggregate (.record (mapEntryFields key element))
      [.data (.prim key.toPrimitive) payload, value])) ?_ ?_ checkNext canonNext finish done
  · intro reached pointer bytes width sized aligned bounds payload value allowed idx valid
    obtain ⟨valueType, entryPath⟩ := allowed
    by_cases stringKey : key = .string
    · subst key
      rw [liveCollectionMapEntry, ite_eq_left (show WIT.KeyType.string = .string from rfl)]
      exact stringMapSlotRule destination inst element output root source.layout source.fits source.allocator reached pointer bytes
        entries.length width sized aligned bounds payload value valueType entryPath idx valid compare embedder
    · have keyData : LocalDataType (.prim key.toPrimitive) := .primitive (by
        cases key <;> first | exact (stringKey rfl).elim | intro impossible; cases impossible)
      rw [liveCollectionMapEntry, ite_eq_right stringKey]
      intro checked canonical last left right check canon frame growth rule doneAt checkAt canonAt
      exact liveMapEntry destination inst key element output keyData payload value reached pointer bytes entries.length idx
        width sized aligned bounds valid compare checked canonical last frame growth doneAt valueType rule checkAt canonAt
  · intro item member
    obtain ⟨payload, value, shape, layout, emitted⟩ := shapes item member
    have entryPath : Field.Descendant root (.aggregate (.record (mapEntryFields key element))
        [.data (.prim key.toPrimitive) payload, value]) := path.trans (.dynamic (shape ▸ member) (.self _))
    have valuePath : Field.Descendant root value := entryPath.trans (.aggregate (by simp) (.self _))
    exact ⟨payload, value, shape, ⟨layout.type_eq, entryPath⟩, child value valuePath layout emitted⟩

private theorem placementInterval (destination : RecordDestination) (before : CStore (core3 grow))
    (area : Layout) (address : Nat) (placed : placement destination before area address = .ok ()) :
    address % area.alignment.bytes = 0 ∧ ∃ bytes,
      (core3 grow).memSize? before.core destination.memory = some bytes ∧ address + area.size ≤ bytes := by
  have aligned : address % area.alignment.bytes = 0 := by
    by_contra invalid
    simp [placement, invalid] at placed
    change Except.error TrapReason.unalignedPointer = .ok () at placed
    contradiction
  cases sized : (core3 grow).memSize? before.core destination.memory with
  | none => simp [placement, aligned, sized] at placed
  | some bytes =>
    refine ⟨aligned, bytes, rfl, ?_⟩
    by_contra invalid
    simp [placement, aligned, sized, Nat.lt_of_not_ge invalid] at placed

private theorem sumArmPlacement (destination : RecordDestination) (type : Stored.TypeOf)
    (arms : List (Option Stored.TypeOf)) (item : Field) (address : Nat) {before after : CStore (core3 grow)}
    (shape : layout destination.width type = variantLayout (arms.map (layoutOption destination.width)))
    (member : some (layout destination.width item.type) ∈ arms.map (layoutOption destination.width))
    (placed : placement destination before (layout destination.width type) address = .ok ())
    (growth : Core3.Grows before.core after.core) :
    placement destination after (layout destination.width item.type) (sumPayloadAddress destination.width arms address) = .ok () := by
  rw [shape] at placed
  let area := variantLayout (arms.map (layoutOption destination.width))
  obtain ⟨aligned, bytes, sized, bounds⟩ := placementInterval destination before area address placed
  obtain ⟨modulo, within⟩ := variantLayout_payload_fits _ address (layout destination.width item.type)
    (Nat.dvd_of_mod_eq_zero aligned) member
  rw [List.length_map] at modulo within
  obtain ⟨reachedBytes, reachedSize, larger⟩ := growth.memSize sized
  have sizeAt : (core3 grow).memSize? after.core destination.memory = some reachedBytes := reachedSize
  have fits : sumPayloadAddress destination.width arms address + (layout destination.width item.type).size ≤ reachedBytes :=
    within.trans (bounds.trans larger)
  change sumPayloadAddress destination.width arms address % (layout destination.width item.type).alignment.bytes = 0 at modulo
  simp [placement, modulo, sizeAt, Nat.not_lt.mpr fits]
  rfl

private theorem liveSumRule (destination : RecordDestination) (inst : InstId) (type : Stored.TypeOf)
    (arms : List (Option Stored.TypeOf)) (tag address : Nat) (selected : Option Field)
    (compare : FieldComparison grow sig)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (child : ∀ item, selected = some item →
      layout destination.width type = variantLayout (arms.map (layoutOption destination.width)) ∧
      some (layout destination.width item.type) ∈ arms.map (layoutOption destination.width) ∧
      PlacedFieldRule compare older origin destination inst item (sumPayloadAddress destination.width arms address)) :
    PlacedFieldRule (fun _ index address left right check canon checkNext canonNext finish =>
      LiveSumThen profile ready base bindings destination inst compare arms selected index address checkNext canonNext finish
        left right check canon) older origin destination inst (.sum type arms tag selected) address := by
  intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
  have widthAt : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width := frame.store ▸ width
  obtain ⟨store, result, lhsLabels, rhsLabels, lhs, rhs, observed, cut⟩ :=
    memory_sum_tag_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst type arms tag index address selected
      left.store left right check canon checkNext canonNext frame.store frame.thread
      (by simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, widthAt])
      (frame.store ▸ Core3.Grows.refl left.store.core) checkAt canonAt
  refine ⟨store, result, lhsLabels, rhsLabels, lhs, rhs.steps, observed, ?_⟩
  cases result with
  | error reason => exact cut
  | ok value =>
    cases value
    obtain ⟨grew, checkTracks, canonTracks⟩ := cut
    refine ⟨checkTracks, canonTracks, ?_⟩
    cases selected with
    | none =>
      exact ends _ _ check canon
        ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        (growth.trans grew) rfl rfl
    | some item =>
      obtain ⟨shape, member, rule⟩ := child item rfl
      let addr := sumPayloadAddress destination.width arms address
      let atChild := localLeafEnd left left.host store check.thread check.frames check.rest
        (sumCheckedNext destination inst (some item) index addr checkNext) (.ok ())
      let atCanonChild := localLeafEnd right right.host store canon.thread canon.frames canon.rest
        (sumCanonicalNext destination inst (some item) addr canonNext) (.ok ())
      exact rule 0 (aggregateNext index checkNext) canonNext atChild atCanonChild check canon
        ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        (growth.trans grew) (grew.memAddrType width) (sumArmPlacement destination type arms item address shape member placed grew)
        rfl rfl finish ends

private theorem optionCompiled {item : Field} {element : Stored.TypeOf}
    (matched : item.LayoutMatches (.option element)) (emitted : item.Emitted) :
    item = .sum (.option element) [none, some element] 0 none ∨
      ∃ child, item = .sum (.option element) [none, some element] 1 (some child) ∧
        child.LayoutMatches element ∧ child.Emitted := by
  cases emitted with
  | sum compiled =>
    cases matched with
    | optionNone => exact .inl rfl
    | optionSome matching => exact .inr ⟨_, rfl, matching, compiled _ rfl⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | _ => cases matched

private theorem resultCompiled {item : Field} {success failure : Option Stored.TypeOf}
    (matched : item.LayoutMatches (.result success failure)) (emitted : item.Emitted) :
    ∃ tag selected, item = .sum (.result success failure) [success, failure] tag selected ∧
      (tag = 0 ∧ Field.ArmMatches selected success ∨ tag = 1 ∧ Field.ArmMatches selected failure) ∧
      ∀ child, selected = some child → child.Emitted := by
  cases emitted with
  | sum compiled =>
    cases matched with
    | resultOk arm => exact ⟨0, _, rfl, .inl ⟨rfl, arm⟩, compiled⟩
    | resultError arm => exact ⟨1, _, rfl, .inr ⟨rfl, arm⟩, compiled⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | _ => cases matched

private theorem fixedCompiled {item : Field} {element : Stored.TypeOf} {length : Nat}
    (matched : item.LayoutMatches (.fixedList element length)) (emitted : item.Emitted) :
    ∃ entries, item = .fixed element length entries ∧ entries.length = length ∧
      Field.EntriesMatch entries element ∧ ∀ entry ∈ entries, entry.Emitted := by
  cases emitted with
  | fixed compiled => cases matched with | fixed count matching => exact ⟨_, rfl, count, matching, compiled⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | _ => cases matched

private theorem liveFixedRule (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (length : Nat) (entries : List Field) (address : Nat)
    (count : entries.length = length) (matching : Field.EntriesMatch entries element) (compare : FieldComparison grow sig)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (child : ∀ item ∈ entries, ∀ reached slot, PlacedFieldRule compare older reached destination inst item slot) :
    PlacedFieldRule (fun _ index address left right check canon checkNext canonNext finish =>
      LiveFixedThen profile ready base bindings destination inst compare element entries index address checkNext canonNext finish
        left right check canon) older origin destination inst (.fixed element length entries) address := by
  intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
  let area := layout destination.width element
  let cx : LiftLowerContext (core3 grow) := destination.context inst
  let body := fun reached => CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries .value
    (layout reached element).size address >>= canonNext
  let reference := { right with ctl := canon.control (body destination.width) }
  have widthAt : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width := frame.store ▸ width
  have reachedWidth : ptrTypeIn right.store cx = destination.width := by
    simp [cx, ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, widthAt]
  have focus : right.ctl = canon.control (.op .get (fun store => body (ptrTypeIn store cx))) := by
    rw [canonAt, CanonicalTree.field]
    let elements : AddrType → Session grow sig Unit := fun reached => CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries .value
      (layout reached element).size address
    change canon.control (((ptrType cx).bind elements).bind canonNext) = _
    rw [Prog.bind_assoc]
    rfl
  refine ⟨fun depth => ?_, ?_⟩
  · change Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right (.active 0 depth) [.tau] reference (.active 0 depth)
    simpa only [reachedWidth, Cursor.control, reference] using (ReturnFrame.Occurrence.Prefix.read (profile := profile)
      (ready := ready) (dispatch := specDispatch ready (LiveDispatch.host bindings base)) depth focus)
  · obtain ⟨modulo, bytes, sized, fits⟩ := placementInterval destination left.store
      (layout destination.width (.fixedList element length)) address placed
    rw [layout] at modulo fits
    have aligned : address = alignTo address area.alignment := by
      change address % area.alignment.bytes = 0 at modulo
      cases reached : area.alignment <;> simp only [alignTo, reached, Alignment.bytes] at modulo ⊢ <;> omega
    have bounds : address + entries.length * area.size ≤ bytes := by
      rw [count]
      simpa only [area, Layout.size, Nat.mul_assoc] using fits
    have checkBody : left.ctl = check.control (Track.checked (.elements area.size) destination inst entries 0 address >>=
        aggregateNext index checkNext) := by
      rw [checkAt, Record.Effects.field]
      let elements : Session grow sig (Except RecordLower.Issue Unit) := Track.checked (.elements area.size) destination inst entries 0 address
      change check.control ((elements.bind fun verdict => Prog.pure (verdict.mapError (.nested index))).bind checkNext) = _
      rw [Prog.bind_assoc]
      rfl
    have done := fun lhs rhs cursor peer paired grew checked canonical =>
      ends lhs rhs cursor peer paired (growth.trans grew) checked canonical
    change liveElements destination inst area.size compare (aggregateNext index checkNext) canonNext finish
      entries 0 address left reference check canon
    simpa only [Nat.zero_mul, Nat.add_zero, aggregateNext] using
      liveElementsRule destination inst element entries 0 address entries.length 0 bytes compare older left.store
        width sized aligned bounds (Nat.zero_add _).le
        (fun item member => (entries_match_of_mem matching member).type_eq) (fun item member => child item member left.store)
        (aggregateNext index checkNext) canonNext finish done
        (left := left) (right := reference) (check := check) (canon := canon)
        ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        (Core3.Grows.refl _) (by simpa only [Nat.zero_mul, Nat.add_zero, Track.checked, area] using checkBody)
        (by simp only [reference, body, cx, Nat.zero_mul, Nat.add_zero])

private theorem variantCompiled {item : Field} {cases : List (String × Option Stored.TypeOf)}
    (matched : item.LayoutMatches (.variant cases)) (emitted : item.Emitted) :
    ∃ tag selected arm, item = .sum (.variant cases) (cases.map Prod.snd) tag selected ∧
      (cases.map Prod.snd)[tag]? = some arm ∧ Field.ArmMatches selected arm ∧
      ∀ child, selected = some child → child.Emitted := by
  cases emitted with
  | sum compiled => cases matched with | variant found matching => exact ⟨_, _, _, rfl, found, matching, compiled⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | _ => cases matched

private theorem variantLayouts (width : AddrType) (cases : List (String × Option Stored.TypeOf)) :
    layoutCases width cases = (cases.map Prod.snd).map (layoutOption width) := by
  induction cases with
  | nil => simp only [layoutCases, List.map_nil]
  | cons entry rest ih => rcases entry with ⟨_, _⟩; simp only [layoutCases, List.map_cons, ih]

private theorem liveVariantArmLookup (destination : RecordDestination) (inst : InstId)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {cases : List (String × Option Stored.TypeOf)} {tag : Nat} {type : Stored.TypeOf}
    (found : (cases.map Prod.snd)[tag]? = some (some type)) :
    (∃ name, (name, some type) ∈ cases) ∧
    liveVariantArm profile ready base bindings older destination inst cases tag =
      liveCollectionField profile ready base bindings older destination inst type := by
  induction cases generalizing tag with
  | nil => simp at found
  | cons entry rest ih =>
    rcases entry with ⟨name, arm⟩
    cases tag with
    | zero =>
      have selected : arm = some type := by simpa using found
      subst arm
      exact ⟨⟨name, by simp⟩, by rw [liveVariantArm]⟩
    | succ index =>
      have ⟨⟨name, member⟩, comparison⟩ := ih (tag := index) (by simpa using found)
      exact ⟨⟨name, List.mem_cons_of_mem _ member⟩, by rw [liveVariantArm, comparison]⟩

private theorem compiledFieldMember {items : List Field} {types : List Stored.TypeOf}
    (matching : Field.FieldsMatch items types) {item : Field} (member : item ∈ items) :
    ∃ type ∈ types, item.LayoutMatches type := by
  induction items generalizing types with
  | nil => simp at member
  | cons first rest ih =>
    cases matching with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self .., head⟩
      · obtain ⟨type, mem, child⟩ := ih tail later
        exact ⟨type, List.mem_cons_of_mem _ mem, child⟩

private theorem recordCompiled {item : Field} {types : List (String × Stored.TypeOf)}
    (matched : item.LayoutMatches (.record types)) (emitted : item.Emitted) :
    ∃ fields, item = .aggregate (.record types) fields ∧ Field.FieldsMatch fields (types.map Prod.snd) ∧
      ∀ child ∈ fields, child.Emitted := by
  cases emitted with
  | aggregate compiled => cases matched with | record matching => exact ⟨_, rfl, matching, compiled⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | _ => cases matched

private theorem tupleCompiled {item : Field} {types : List Stored.TypeOf}
    (matched : item.LayoutMatches (.tuple types)) (emitted : item.Emitted) :
    ∃ fields, item = .aggregate (.tuple types) fields ∧ Field.FieldsMatch fields types ∧
      ∀ child ∈ fields, child.Emitted := by
  cases emitted with
  | aggregate compiled => cases matched with | tuple matching => exact ⟨_, rfl, matching, compiled⟩
  | @endpoint channel _ _ => cases channel <;> cases matched
  | _ => cases matched

private theorem flatDataPaths (destination : RecordDestination) (inst : InstId) (type : Stored.TypeOf)
    (data : LocalDataType type) (payload : Stored.Payload type) {older origin start incoming offset sink}
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width) :
    DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset destination inst sink
      (fun _ _ _ _ finish before _ _ _ _ => LocalPathsThen profile ready base bindings start incoming before offset (flatWordVisit finish))
      (.data type payload) := by
  intro index checkNext canonNext finish before left right check canon frame growth leading _ checkAt canonAt ends
  have width := growth.memAddrType memoryWidth
  obtain ⟨store, result, lhsTrace, rhsTrace, lhs, rhs, observed, cut⟩ :=
    local_data_leaf_frame_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) destination inst type data payload index
      .flat origin left right (frame.store ▸ growth)
      (by
        change ((core3 grow).memAddrType? left.store.core destination.memory).getD .i32 = destination.width
        rw [show (core3 grow).memAddrType? left.store.core destination.memory = some destination.width from width]
        rfl) rfl
      frame.store check canon frame.thread checkNext canonNext checkAt canonAt
  cases result with
  | error reason =>
    obtain ⟨labels, trapped⟩ := cut
    exact .inl ⟨reason, labels, _, _, CallbackPrefix.appendComparedPaths leading
      ⟨lhsTrace, rhsTrace, lhs, rhs.steps, observed.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok words =>
    obtain ⟨grew, checkTracks, canonTracks⟩ := cut
    have trails := CallbackPrefix.appendComparedSlots leading ⟨lhsTrace, rhsTrace, checkTracks, canonTracks, rfl, observed.symm⟩
    exact .inr ⟨visible lhsTrace, _, _, check, canon, trails, rfl, words, ends words _ _ _ _ _
      ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ grew trails rfl rfl⟩

private theorem flatStringPaths (destination : RecordDestination) (inst : InstId) (str : LinkedCallback.StringField)
    {root rootSchema} (source : CollectionSource destination root rootSchema) (path : Field.Descendant root str.field)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {older origin start incoming offset sink}
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width) :
    DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset destination inst sink
      (liveFlatPaths profile ready base bindings older destination inst start incoming offset sink (.prim .string)) str.field := by
  intro index checkNext canonNext finish before left right check canon frame growth leading _ checkAt canonAt ends
  let keep : List FlatValue → Finish grow sig := fun _ lhs rhs cursor peer =>
    LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧ Core3.Grows origin.core lhs.store.core
  let commit : Nat → Finish grow sig := fun _ => LiveValueCommit profile ready base bindings .flat checkNext canonNext keep
  have body := stringValueThen (profile := profile) (ready := ready) (base := base) (origin := origin)
    destination inst str .flat source path embedder frame growth (growth.memAddrType memoryWidth) rfl checkAt canonAt
    (finish := commit) (fun pointer lhs rhs cursor peer related grew lhsAt rhsAt => by
      obtain ⟨store, outcome, labels, seen, checked, canonical, continued⟩ :=
        stringValueCommit (destination.context inst) destination.width .flat _ pointer related lhsAt rhsAt
      exact ⟨store, outcome, labels, seen, checked, canonical, fun value equal =>
        let ⟨checkTracks, canonTracks, after⟩ := continued value equal
        ⟨checkTracks, canonTracks, after, grew.trans checked.grows⟩⟩)
  refine ⟨str, rfl, CallbackPrefix.stringValuePaths leading body ?_⟩
  intro _ lhs rhs cursor peer observed published tracks
  obtain ⟨store, outcome, labels, seen, checked, canonical, continued⟩ := published
  cases outcome with
  | error reason =>
    have trap := leafTrap seen
    exact .inl ⟨reason, [], _, _, CallbackPrefix.appendComparedPaths tracks
      ⟨labels, labels, checked.steps, canonical.steps, trap, trap, rfl⟩, rfl, rfl⟩
  | ok words =>
    obtain ⟨checkedTracks, canonTracks, paired, grew⟩ := continued words rfl
    have reached := CallbackPrefix.appendComparedSlots tracks ⟨labels, labels, checkedTracks, canonTracks, rfl, rfl⟩
    exact .inr ⟨visible labels, _, _, cursor, peer, reached, rfl, words, ends words _ _ _ _ _ paired grew reached rfl rfl⟩

private theorem selectFlatChild {paths : List (Stored.TypeOf × FlatFieldTrail grow sig)} {type item child}
    {older origin start incoming offset destination inst sink}
    (matching : item.LayoutMatches type) (member : (type, child) ∈ paths)
    (rule : DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset destination inst sink child item) :
    DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset destination inst sink (selectFlatPaths paths) item := by
  intro index checkNext canonNext finish before left right check canon frame grow trails admitted checkAt canonAt ends
  exact ⟨child, matching.type_eq ▸ member, rule index checkNext canonNext finish before left right check canon frame grow trails
    admitted checkAt canonAt ends⟩

private theorem flatAggregateField (destination : RecordDestination) (inst : InstId) (item : Field) (items : List Field)
    {older origin start incoming offset sink child}
    (shape : (∃ type, item = .aggregate type items) ∨ (∃ element length, item = .fixed element length items))
    (rules : ∀ field ∈ items, DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset
      destination inst sink child field) :
    DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset destination inst sink
      (flatAggregatePaths destination inst child) item := by
  rcases shape with ⟨type, rfl⟩ | ⟨element, length, rfl⟩ <;>
    intro index checkNext canonNext finish before left right check canon frame grew trail admitted checkAt canonAt ends <;>
    refine ⟨items, rfl, FlatTrails.aggregate destination inst items index child checkNext canonNext finish rules admitted
      frame grew trail ?_ canonAt ends⟩ <;>
    simpa only [Record.Effects.field, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using! checkAt

private theorem liveRecordMember (destination : RecordDestination) (inst : InstId)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {fields : List (String × Stored.TypeOf)} {name : String} {type : Stored.TypeOf}
    (member : (name, type) ∈ fields) :
    (type, liveCollectionField profile ready base bindings older destination inst type) ∈
      liveRecordFields profile ready base bindings older destination inst fields := by
  induction fields with
  | nil => simp at member
  | cons field rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · rw [liveRecordFields]; exact List.mem_cons_self ..
    · rcases field with ⟨label, schema⟩
      rw [liveRecordFields]
      exact List.mem_cons_of_mem _ (ih later)

private theorem liveTupleMember (destination : RecordDestination) (inst : InstId)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {types : List Stored.TypeOf} {type : Stored.TypeOf}
    (member : type ∈ types) :
    (type, liveCollectionField profile ready base bindings older destination inst type) ∈
      liveTupleFields profile ready base bindings older destination inst types := by
  induction types with
  | nil => simp at member
  | cons field rest ih =>
    rw [liveTupleFields]
    rcases List.mem_cons.mp member with rfl | later
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih later)

private theorem aggregateChildRule {comparisons : List (Stored.TypeOf × FieldComparison grow sig)}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    {destination : RecordDestination} {inst : InstId} {item : Field} {address : Nat} {type : Stored.TypeOf}
    (matching : item.LayoutMatches type) {compare : FieldComparison grow sig} (member : (type, compare) ∈ comparisons)
    (rule : PlacedFieldRule compare older origin destination inst item address) :
    PlacedFieldRule (aggregateChild comparisons) older origin destination inst item address := by
  intro index checkNext canonNext left right check canon frame grew width placed checkAt canonAt finish ends
  exact ⟨compare, matching.type_eq ▸ member, rule index checkNext canonNext left right check canon frame grew width placed
    checkAt canonAt finish ends⟩

private theorem liveAggregateRule (destination : RecordDestination) (inst : InstId) (type : Stored.TypeOf)
    (fields : List Field) (address : Nat) (matching : Field.LayoutMatches (.aggregate type fields) type)
    (compare : FieldComparison grow sig)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (children : ∀ item ∈ fields, ∀ reached slot, PlacedFieldRule compare older reached destination inst item slot) :
    PlacedFieldRule (fun _ index address left right check canon checkNext canonNext finish =>
      LiveAggregateThen profile ready base bindings destination inst compare fields index address checkNext canonNext finish
        left right check canon) older origin destination inst (.aggregate type fields) address := by
  intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
  obtain ⟨aligned, bytes, sized, bounds⟩ := placementInterval destination left.store (layout destination.width type) address placed
  refine aggregate_replay_between (origin := left.store) destination inst type fields index address compare checkNext canonNext
    finish frame (Core3.Grows.refl _) width sized matching aligned bounds ?_ (fun lhs rhs check canon paired grew =>
      ends lhs rhs check canon paired (growth.trans grew)) checkAt canonAt
  intro item member slot fits childIndex childCheck childCanon lhs rhs check canon paired grew checkBody canonBody done next
  obtain ⟨reachedBytes, sizeAt, widened⟩ := grew.memSize sized
  change (core3 grow).memSize? lhs.store.core destination.memory = some reachedBytes at sizeAt
  have placedChild : placement destination lhs.store (layout destination.width item.type) slot = .ok () := by
    simp [placement, fits.1, sizeAt, Nat.not_lt.mpr (fits.2.trans widened)]
    rfl
  exact children item member left.store slot childIndex childCheck childCanon lhs rhs check canon paired grew
    (grew.memAddrType width) placedChild checkBody canonBody done next

private theorem collectionFieldRule (destination : RecordDestination) (inst : InstId)
    {schema : Stored.TypeOf} (family : RecursiveCollectionType schema) (item : Field) (address : Nat)
    (matched : item.LayoutMatches schema) (emitted : item.Emitted) {root : Field} {rootSchema : Stored.TypeOf}
    (source : CollectionSource destination root rootSchema) (path : Field.Descendant root item)
    {origin : CStore (core3 grow)}
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} :
    PlacedFieldRule (liveCollectionField profile ready base bindings older destination inst schema)
      older origin destination inst item address := by
  induction family generalizing item address origin with
  | leaf nominal =>
    intro index checkNext canonNext left right check canon frame growth _ _ checkAt canonAt finish ends
    have leaf := LinkedCallback.ChildFrameOver.handle_field_then_between (profile := profile) (ready := ready)
      (dispatch := specDispatch ready base) (reference := specDispatch ready (LiveDispatch.host bindings base))
      destination inst item (nominalEntry nominal matched emitted) index (.memory address) checkNext canonNext
      frame growth checkAt canonAt (fun _ => ends)
    cases nominal <;> exact leaf
  | @data type data =>
    obtain ⟨payload, rfl⟩ := dataCompiled data matched
    have compared := localFieldThen (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      (older := older) (origin := origin) destination inst type data payload address
    cases data with
    | @primitive prim nonString => cases prim <;> first | exact compared | exact (nonString rfl).elim
    | enum | flags => exact compared
  | string =>
    obtain ⟨str, rfl⟩ := stringCompiled matched emitted
    exact stringFieldThen destination inst str address source path embedder
  | @list element _ ih =>
    obtain ⟨entries, rfl, shapes, compiled⟩ := listCompiled matched emitted
    intro index checkNext canonNext left right check canon frame growth _ _ checkAt canonAt finish ends
    exact ⟨entries, rfl, collectionEntryVisiting destination inst (.list element) element entries index (.memory address)
      checkNext canonNext frame checkAt canonAt embedder _
        (liveListVisitor destination inst element entries index (.memory address) _ older origin left.store growth
          shapes (fun child member _ slot => ih child slot (entries_match_of_mem shapes member) (compiled child member)
            (path.trans (.dynamic member (.self _)))) checkNext canonNext (fun () => finish) (fun _ => ends))
        (initialSlots left right)⟩
  | @map key element _ ih =>
    obtain ⟨entries, rfl, shapes⟩ := mapCompiled matched emitted
    intro index checkNext canonNext left right check canon frame growth _ _ checkAt canonAt finish ends
    refine ⟨entries, rfl, collectionEntryVisiting destination inst (.map key element) (.record (mapEntryFields key element))
      entries index (.memory address) checkNext canonNext frame checkAt canonAt embedder _
        (liveCompiledMapVisitor destination inst key element entries index (.memory address) _ older left.store source path shapes
          (fun value ancestry layout compiled _ slot => ih value slot layout compiled ancestry) embedder
          checkNext canonNext (fun () => finish) ?_) (initialSlots left right)⟩
    intro _ lhs rhs cursor peer paired kept leftAt rightAt
    exact ends lhs rhs cursor peer paired (growth.trans kept) leftAt rightAt
  | @fixed element length _ ih =>
    obtain ⟨entries, rfl, count, matching, compiled⟩ := fixedCompiled matched emitted
    have rule := liveFixedRule (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      (older := older) (origin := origin) destination inst element length entries address count matching
      (liveCollectionField profile ready base bindings older destination inst element)
      (fun item member _ slot => ih item slot (entries_match_of_mem matching member) (compiled item member)
        (path.trans (.fixed member (.self _))))
    intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
    exact ⟨entries, rfl, rule index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends⟩
  | @option element _ ih =>
    have compare := fun tag selected => liveSumRule (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      (older := older) (origin := origin) destination inst (.option element) [none, some element] tag address selected
      (liveCollectionField profile ready base bindings older destination inst element)
    rcases optionCompiled matched emitted with rfl | ⟨item, rfl, matching, compiled⟩
    ·
      have rule := compare 0 none (by intros; contradiction)
      intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
      exact ⟨0, none, rfl, rule index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends⟩
    ·
      have rule := compare 1 (some item) (by
        intro child equal
        cases equal
        refine ⟨by simp only [layout, List.map_cons, List.map_nil, layoutOption], ?_, ?_⟩
        · simp [matching.type_eq, layoutOption]
        · exact ih item _ matching compiled (path.trans (.sum (.self _))))
      intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
      exact ⟨1, some item, rfl, rule index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends⟩
  | @result success failure _ _ ihOk ihErr =>
    obtain ⟨tag, selected, rfl, arm, compiled⟩ := resultCompiled matched emitted
    let comparison (schema : Option Stored.TypeOf) : FieldComparison grow sig := match schema with
      | some type => liveCollectionField profile ready base bindings older destination inst type
      | none => fun _ _ _ _ _ _ _ _ _ _ => False
    have branch (schema : Option Stored.TypeOf) (matched : Field.ArmMatches selected schema)
        (mem : schema ∈ [success, failure])
        (derive : ∀ type, schema = some type → ∀ item address, item.LayoutMatches type → item.Emitted →
          Field.Descendant root item → PlacedFieldRule (liveCollectionField profile ready base bindings older destination inst type)
            older origin destination inst item address) :
        ∀ item, selected = some item →
          layout destination.width (.result success failure : Stored.TypeOf) = variantLayout ([success, failure].map (layoutOption destination.width)) ∧
          some (layout destination.width item.type) ∈ [success, failure].map (layoutOption destination.width) ∧
          PlacedFieldRule (comparison schema) older origin destination inst item
            (sumPayloadAddress destination.width [success, failure] address) := by
      intro item equal
      cases matched with
      | none => contradiction
      | @some field type matching =>
        cases equal
        refine ⟨by simp only [layout, List.map_cons, List.map_nil], ?_, ?_⟩
        · exact List.mem_map.mpr ⟨some type, mem, by rw [matching.type_eq, layoutOption]⟩
        · exact derive type rfl _ _ matching (compiled _ rfl) (path.trans (.sum (.self _)))
    have child : ∀ item, selected = some item →
        layout destination.width (.result success failure : Stored.TypeOf) = variantLayout ([success, failure].map (layoutOption destination.width)) ∧
        some (layout destination.width item.type) ∈ [success, failure].map (layoutOption destination.width) ∧
        PlacedFieldRule (if tag = 0 then comparison success else comparison failure) older origin destination inst item
          (sumPayloadAddress destination.width [success, failure] address) := by
      rcases arm with ⟨rfl, matching⟩ | ⟨rfl, matching⟩
      · simpa using branch success matching (by simp) (fun type equal item slot shape emitted ancestry =>
          ihOk type equal item slot shape emitted ancestry)
      · simpa using branch failure matching (by simp) (fun type equal item slot shape emitted ancestry =>
          ihErr type equal item slot shape emitted ancestry)
    intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
    have compared := liveSumRule (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst (.result success failure) [success, failure] tag address selected
      (if tag = 0 then comparison success else comparison failure) child index checkNext canonNext left right check canon
      frame growth width placed checkAt canonAt finish ends
    cases success <;> cases failure <;> exact ⟨tag, selected, rfl, compared⟩
  | @variant cases _ ih =>
    obtain ⟨tag, selected, arm, rfl, found, matching, compiled⟩ := variantCompiled matched emitted
    let arms := cases.map Prod.snd
    let compare := liveVariantArm profile ready base bindings older destination inst cases tag
    have child : ∀ item, selected = some item →
        layout destination.width (.variant cases : Stored.TypeOf) = variantLayout (arms.map (layoutOption destination.width)) ∧
        some (layout destination.width item.type) ∈ arms.map (layoutOption destination.width) ∧
        PlacedFieldRule compare older origin destination inst item (sumPayloadAddress destination.width arms address) := by
      intro item equal
      cases matching with
      | none => contradiction
      | @some field type exactLayout =>
        cases equal
        obtain ⟨⟨name, member⟩, compared⟩ := liveVariantArmLookup (profile := profile) (ready := ready)
          (base := base) (bindings := bindings) (older := older) destination inst found
        refine ⟨by rw [layout, variantLayouts], ?_, ?_⟩
        · exact List.mem_map.mpr ⟨some type, List.mem_map.mpr ⟨(name, some type), member, rfl⟩,
            by rw [exactLayout.type_eq, layoutOption]⟩
        · change PlacedFieldRule (liveVariantArm profile ready base bindings older destination inst cases tag)
            older origin destination inst item _
          rw [compared]
          exact ih name type member item _ exactLayout (compiled item rfl) (path.trans (.sum (.self _)))
    intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
    exact ⟨tag, selected, rfl, liveSumRule destination inst (.variant cases) arms tag address selected compare child
      index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends⟩
  | @record types _ ih =>
    obtain ⟨fields, rfl, matching, compiled⟩ := recordCompiled matched emitted
    have rule := liveAggregateRule (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst (.record types) fields address (.record matching)
      (aggregateChild (liveRecordFields profile ready base bindings older destination inst types)) (origin := origin) (older := older) (by
        intro child member reached slot
        obtain ⟨type, included, layout⟩ := compiledFieldMember matching member
        obtain ⟨⟨name, _⟩, belongs, rfl⟩ := List.mem_map.mp included
        exact aggregateChildRule layout (liveRecordMember destination inst belongs)
          (ih name _ belongs child slot layout (compiled child member) (path.trans (.aggregate member (.self _)))))
    intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
    exact ⟨fields, rfl, rule index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends⟩
  | @tuple types _ ih =>
    obtain ⟨fields, rfl, matching, compiled⟩ := tupleCompiled matched emitted
    have rule := liveAggregateRule (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst (.tuple types) fields address (.tuple matching)
      (aggregateChild (liveTupleFields profile ready base bindings older destination inst types)) (origin := origin) (older := older) (by
        intro child member reached slot
        obtain ⟨type, included, layout⟩ := compiledFieldMember matching member
        exact aggregateChildRule layout (liveTupleMember destination inst included)
          (ih type included child slot layout (compiled child member) (path.trans (.aggregate member (.self _)))))
    intro index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends
    exact ⟨fields, rfl, rule index checkNext canonNext left right check canon frame growth width placed checkAt canonAt finish ends⟩

private theorem flatCompiledField (destination : RecordDestination) (inst : InstId)
    {schema : Stored.TypeOf} (family : RecursiveCollectionType schema) (item : Field)
    (matched : item.LayoutMatches schema) (emitted : item.Emitted) {root rootSchema}
    (source : CollectionSource destination root rootSchema) (path : Field.Descendant root item)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {older origin start incoming offset sink}
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (covers : sink.Covers profile ready base bindings start incoming offset) :
    DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset destination inst sink
      (liveFlatPaths profile ready base bindings older destination inst start incoming offset sink schema) item := by
  induction family generalizing item with
  | @data type data =>
    obtain ⟨payload, rfl⟩ := dataCompiled data matched
    have compared := flatDataPaths (sink := sink) (offset := offset) (older := older) (start := start) (incoming := incoming)
      (profile := profile) (ready := ready) (base := base) (bindings := bindings) destination inst type data payload memoryWidth
    cases data with
    | @primitive prim nonString => cases prim <;> first | exact compared | exact (nonString rfl).elim
    | enum | flags => exact compared
  | leaf nominal =>
    have handle := nominalEntry nominal matched emitted
    cases nominal <;>
      intro index checkNext canonNext finish before left right check canon frame growth trail admitted checkAt canonAt ends <;>
      exact CallbackPrefix.handleValuePaths trail frame.store
        (LinkedCallback.ChildFrameOver.handle_field_then_between destination inst item handle index .flat
          checkNext canonNext frame growth checkAt canonAt (fun words lhs rhs cursor peer paired grew lhsAt rhsAt =>
            ⟨paired, grew, lhsAt, rhsAt⟩ : ∀ words lhs rhs cursor peer, _ → _ → _ → _ →
              LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧ Core3.Grows origin.core lhs.store.core ∧
              lhs.ctl = cursor.control (checkNext (.ok words)) ∧ rhs.ctl = peer.control (canonNext words)))
        covers admitted (fun words seen lhs rhs cursor peer reached _ ⟨paired, grew, lhsAt, rhsAt⟩ =>
          ⟨words, ends words seen lhs rhs cursor peer paired grew reached lhsAt rhsAt⟩)
  | string =>
    obtain ⟨str, rfl⟩ := stringCompiled matched emitted
    exact flatStringPaths destination inst str source path embedder memoryWidth
  | @list element family _ =>
    obtain ⟨entries, rfl, shapes, compiled⟩ := listCompiled matched emitted
    intro index checkNext canonNext finish before left right check canon frame growth leading admitted checkAt canonAt ends
    let compare := liveCollectionField profile ready base bindings older destination inst element
    let done : ValueFinish grow sig .flat := fun words lhs rhs cursor peer =>
      LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧ Core3.Grows origin.core lhs.store.core ∧
      lhs.ctl = cursor.control (checkNext (.ok words)) ∧ rhs.ctl = peer.control (canonNext words)
    have visitor := liveListVisitor (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst element entries index .flat compare older origin left.store growth shapes
      (fun child member _ address => collectionFieldRule destination inst family child address
        (entries_match_of_mem shapes member) (compiled child member) source (path.trans (.dynamic member (.self _))) embedder)
      checkNext canonNext done (fun _ _ _ _ _ paired grew lhsAt rhsAt => ⟨paired, grew, lhsAt, rhsAt⟩)
    have body := collectionEntryVisiting (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst (.list element) element entries index .flat
      checkNext canonNext frame checkAt canonAt embedder _ visitor (initialSlots left right)
    refine ⟨entries, rfl, RecursiveTrails.collectionEntryPaths covers admitted leading body ?_⟩
    intro pointer bytes observed lhs rhs cursor peer reached shared elements
    exact CallbackPrefix.liveElementsPathsFrom (RecursiveTrails.fieldPaths covers family) reached shared elements
      (sink.nested _ admitted index) (fun _ _ _ _ _ terminal _ publish => RecursiveTrails.descriptorPaths terminal publish
        (fun words seen lhs rhs cursor peer tracks _ ⟨paired, grew, lhsAt, rhsAt⟩ =>
          ⟨words, ends words seen lhs rhs cursor peer paired grew tracks lhsAt rhsAt⟩))
  | @map key element family _ =>
    obtain ⟨entries, rfl, shapes⟩ := mapCompiled matched emitted
    intro index checkNext canonNext finish before left right check canon frame growth leading admitted checkAt canonAt ends
    let compare := liveCollectionField profile ready base bindings older destination inst element
    let done : ValueFinish grow sig .flat := fun words lhs rhs cursor peer =>
      LinkedCallback.ChildFrameOver older lhs rhs cursor peer ∧ Core3.Grows origin.core lhs.store.core ∧
      lhs.ctl = cursor.control (checkNext (.ok words)) ∧ rhs.ctl = peer.control (canonNext words)
    have visitor := liveCompiledMapVisitor (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst key element entries index .flat compare older left.store source path shapes
      (fun value ancestry layout compiled _ address => collectionFieldRule destination inst family value address
        layout compiled source ancestry embedder) embedder checkNext canonNext done
      (fun _ _ _ _ _ paired grew lhsAt rhsAt => ⟨paired, growth.trans grew, lhsAt, rhsAt⟩)
    have body := collectionEntryVisiting (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      destination inst (.map key element) (.record (mapEntryFields key element)) entries index .flat
      checkNext canonNext frame checkAt canonAt embedder _ visitor (initialSlots left right)
    refine ⟨entries, rfl, RecursiveTrails.collectionEntryPaths covers admitted leading body ?_⟩
    intro pointer bytes observed lhs rhs cursor peer reached shared elements
    exact RecursiveTrails.mapElementsPaths (RecursiveTrails.fieldPaths covers family) reached shared elements
      (sink.nested _ admitted index) (fun _ _ _ _ _ terminal _ publish => RecursiveTrails.descriptorPaths terminal publish
        (fun words seen lhs rhs cursor peer tracks _ ⟨paired, grew, lhsAt, rhsAt⟩ =>
          ⟨words, ends words seen lhs rhs cursor peer paired grew tracks lhsAt rhsAt⟩))
  | fixed _ ih =>
    obtain ⟨children, rfl, _, matching, compiled⟩ := fixedCompiled matched emitted
    exact flatAggregateField destination inst _ children (.inr ⟨_, _, rfl⟩) fun child member =>
      ih child (entries_match_of_mem matching member) (compiled child member) (path.trans (.fixed member (.self _)))
  | @option element _ ih =>
    rcases optionCompiled matched emitted with rfl | ⟨child, rfl, matching, compiled⟩
    · exact FlatTrails.sum destination inst (.option element) [none, some element] 0 none (by change 0 < 2; decide) _
        (fun _ impossible => nomatch impossible)
    · exact FlatTrails.sum destination inst (.option element) [none, some element] 1 (some child) (by change 1 < 2; decide) _
        (fun _ equal => by cases equal; exact ih child matching compiled (path.trans (.sum (.self _))))
  | @result success failure _ _ ihSuccess ihFailure =>
    obtain ⟨tag, selected, rfl, chosen, compiled⟩ := resultCompiled matched emitted
    have valid : tag < [success, failure].length := by
      change tag < 2
      rcases chosen with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
    let armPaths : Option Stored.TypeOf → FlatFieldTrail grow sig
      | none => noFlatChild
      | some type => liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type
    have pathsEq : liveFlatPaths profile ready base bindings older destination inst start incoming offset sink (.result success failure) =
        flatSumPaths profile ready base bindings start incoming offset destination.width (.result success failure) [success, failure]
          (fun tag => if tag = 0 then armPaths success else armPaths failure) := by
      cases success <;> cases failure <;> rfl
    rw [pathsEq]
    refine FlatTrails.sum destination inst (.result success failure) [success, failure] tag selected valid
      (fun tag => if tag = 0 then armPaths success else armPaths failure) ?_
    intro child equal
    rcases chosen with ⟨rfl, matching⟩ | ⟨rfl, matching⟩
    · cases matching with
      | none => contradiction
      | some matching =>
        cases equal
        exact ihSuccess _ rfl child matching (compiled child rfl) (path.trans (.sum (.self _)))
    · cases matching with
      | none => contradiction
      | some matching =>
        cases equal
        exact ihFailure _ rfl child matching (compiled child rfl) (path.trans (.sum (.self _)))
  | @variant cases _ ih =>
    obtain ⟨tag, selected, arm, rfl, found, matching, compiled⟩ := variantCompiled matched emitted
    have valid : tag < (cases.map Prod.snd).length := by
      by_contra outside
      rw [List.getElem?_eq_none (Nat.le_of_not_lt outside)] at found
      contradiction
    refine FlatTrails.sum destination inst (.variant cases) (cases.map Prod.snd) tag selected valid _ ?_
    intro child equal
    cases matching with
    | none => contradiction
    | @some field type layout =>
      cases equal
      obtain ⟨⟨name, member⟩, compared⟩ := FlatTrails.variantMember (profile := profile) (ready := ready)
        (base := base) (bindings := bindings) (older := older) (start := start) (incoming := incoming) (offset := offset)
        (sink := sink) destination inst found
      rw [compared]
      exact ih name type member _ layout (compiled _ rfl) (path.trans (.sum (.self _)))
  | record _ ih =>
    obtain ⟨children, rfl, matching, compiled⟩ := recordCompiled matched emitted
    apply flatAggregateField destination inst _ children (.inl ⟨_, rfl⟩)
    intro child member
    obtain ⟨type, declared, layout⟩ := compiledFieldMember matching member
    obtain ⟨⟨name, schema⟩, present, rfl⟩ := List.mem_map.mp declared
    exact selectFlatChild layout (FlatTrails.recordMember destination inst _ present)
      (ih name schema present child layout (compiled child member) (path.trans (.aggregate member (.self _))))
  | tuple _ ih =>
    obtain ⟨children, rfl, matching, compiled⟩ := tupleCompiled matched emitted
    apply flatAggregateField destination inst _ children (.inl ⟨_, rfl⟩)
    intro child member
    obtain ⟨type, declared, layout⟩ := compiledFieldMember matching member
    exact selectFlatChild layout (FlatTrails.tupleMember destination inst _ declared)
      (ih type declared child layout (compiled child member) (path.trans (.aggregate member (.self _))))

theorem linkedStringMapEntry {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (index : Fin entries.length)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (origin : CStore (core3 grow)) (basePtr bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? origin.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (next : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop)
    (follow : ∀ lhs rhs cursor peer, LinkedCallback.ChildFrameOver older lhs rhs cursor peer →
      Core3.Grows origin.core lhs.store.core →
      (let stride := (layout site.destination.width (.record (mapEntryFields .string element))).size
       let addr := basePtr + index.val * stride + stride
       let cx := site.destination.context site.inst
       let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
       lhs.ctl = cursor.control (Record.Effects.elements recordClaims Limits.spec Quirks.none cx site.destination.width
         (entries.drop (index.val + 1)) stride addr (index.val + 1) >>= checkNext) →
       rhs.ctl = peer.control (CanonicalTree.elements Limits.spec Quirks.none cx site.destination.width
         (entries.drop (index.val + 1)) mode stride addr >>= canonNext) → next lhs rhs cursor peer)) :
    LinkedStringMapEntry profile ready base bindings older site element entries index origin basePtr left right check canon
      checkNext canonNext next := by
  unfold LinkedStringMapEntry
  intro destination cx type stride ptr mode item rest checkTail canonTail checkAt canonAt
  obtain ⟨plan, compiled⟩ := linked.compiled
  have rootLayout := Record.preflightValue_layout _ _ _ _ _ plan compiled
  have rootFits := Record.preflightValue_value _ _ _ _ _ plan compiled ▸ fits
  have rootEmitted := linked.emitted
  have childLayout := field ▸ rootLayout
  rw [field] at rootEmitted
  have member : item ∈ entries := List.getElem_mem _
  cases rootEmitted with
  | map shape emitted =>
    obtain ⟨keyPayload, value, selected⟩ := shape item member
    have valid := emitted keyPayload value (selected ▸ member)
    have matched := mapValueLayout (selected ▸ entries_match_of_mem (mapEntries childLayout) member)
    obtain ⟨str, typed⟩ := keyPayload
    cases typed with
    | int kind _ => cases kind
    | string validString =>
      let key : LinkedCallback.StringField := ⟨_, validString⟩
      have path : Field.Descendant site.field (.aggregate type [key.field, value]) := by
        rw [field]
        exact .dynamic (selected ▸ member) (.self _)
      refine ⟨key, value, selected, ?_⟩
      have keyRun := stringMapKey (profile := profile) (ready := ready) (base := base) (bindings := bindings)
        destination site.inst element route.output key value site.field rootLayout rootFits (preflightAllocator site linked) path
        origin basePtr bytes entries.length index.val index.val width sized aligned bounds index.isLt checkTail canonTail frame growth embedder
      have selectedDrop : entries.drop index.val = .aggregate type [key.field, value] :: rest :=
        (List.drop_eq_getElem_cons index.isLt).trans (congrArg (· :: rest) selected)
      have atCheck : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
          (.aggregate type [key.field, value]) index.val (.memory ptr) >>= checkTail) := by
        rw [checkAt, selectedDrop, Record.Effects.elements]
        congr 1
        simp only [Prog.bind_eq, Prog.bind_assoc, checkTail]
        congr 1
        funext verdict
        cases verdict with
        | error _ => rfl
        | ok result => cases result; rfl
      have atCanon := canonAt
      rw [selectedDrop] at atCanon
      refine mapStringKeyFinish _ _ _ _ _ _ ?_ (stringKeyNominalValue (profile := profile) (ready := ready) (base := base) (bindings := bindings)
        origin destination site.inst element route.output key value (alignTo ptr (layout destination.width key.field.type).alignment)
        index.val nominal matched valid width checkTail canonTail (keyRun atCheck ?_))
      · intro pointer lhs rhs cursor peer segment
        obtain ⟨reached, outcome, lhsTrace, rhsTrace, leftFinal, rightFinal, lhsRun, rhsRun, same, seen, status⟩ := segment
        refine ⟨reached, outcome, lhsTrace, rhsTrace, leftFinal, rightFinal, lhsRun, rhsRun, same, seen, ?_⟩
        cases outcome with
        | trapped _ | refused _ => exact status
        | returned result =>
          cases result
          obtain ⟨paired, lhsAt, rhsAt, lhsTrail, rhsTrail, grown⟩ := status
          exact ⟨paired, lhsAt, rhsAt, lhsTrail, rhsTrail,
            follow leftFinal rightFinal cursor reached paired grown lhsAt rhsAt⟩
      rw [atCanon]
      apply congrArg canon.control
      let canonRest : Session grow sig Unit := CanonicalTree.elements Limits.spec Quirks.none cx destination.width rest mode stride (ptr + stride)
      let readWidth : Session grow sig AddrType := ptrType cx
      let keySlot := fun reached => alignTo ptr (layout reached key.field.type).alignment
      let keyBody : AddrType → Session grow sig Unit := fun reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width key.field (.memory (keySlot reached))
      let valueBody : AddrType → AddrType → Session grow sig Unit := fun keyWidth reached =>
        CanonicalTree.field Limits.spec Quirks.none cx destination.width value
          (.memory (alignTo (keySlot keyWidth + (layout keyWidth key.field.type).size) (layout reached value.type).alignment))
      cases route with
      | memory address =>
        let reached := destination.width
        change ((keyBody reached).bind (fun _ => (valueBody reached reached).bind (fun _ => canonRest))).bind canonNext =
          (keyBody reached).bind (fun _ => (valueBody reached reached).bind (fun _ => canonRest.bind canonNext))
        simp only [Prog.bind_assoc]
      | flat schema =>
        change ((readWidth.bind (fun keyWidth => (keyBody keyWidth).bind fun _ =>
          readWidth.bind fun reached => (valueBody keyWidth reached).bind fun _ => .pure ())).bind (fun _ => canonRest)).bind canonNext =
          readWidth.bind (fun keyWidth => (keyBody keyWidth).bind fun _ =>
            readWidth.bind fun reached => (valueBody keyWidth reached).bind fun _ => canonRest.bind canonNext)
        simp only [Prog.bind_assoc, Prog.pure_bind']

theorem linkedStringMapTraversal {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (index : Nat)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (origin : CStore (core3 grow)) (basePtr bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? origin.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (atSuffix : LinkedStringMapAt site element entries index basePtr left right check canon checkNext canonNext)
    (finish : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      Cursor (E := core3 grow) (HostState sig) → Cursor (E := core3 grow) (HostState sig) → Prop)
    (atFinish : ∀ lhs rhs cursor peer, LinkedCallback.ChildFrameOver older lhs rhs cursor peer →
      lhs.ctl = cursor.control (checkNext (.ok ())) → rhs.ctl = peer.control (canonNext ()) → finish lhs rhs cursor peer) :
    LinkedStringMapTraversal profile ready base bindings older site element entries index origin basePtr left right check canon
      checkNext canonNext finish := by
  rw [LinkedStringMapTraversal]
  refine ⟨atSuffix, ?_⟩
  split
  next present =>
    refine linkedStringMapEntry site linked element entries ⟨index, present⟩ nominal field fits origin basePtr bytes width sized
      aligned bounds checkNext canonNext frame growth embedder _ ?_
    intro lhs rhs cursor peer paired grown stride addr cx mode checkAt canonAt
    refine linkedStringMapTraversal site linked element entries (index + 1) nominal field fits origin basePtr bytes width sized
      aligned bounds checkNext canonNext paired (paired.store ▸ grown) embedder ?_ finish atFinish
    unfold LinkedStringMapAt
    dsimp only [addr] at checkAt canonAt
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using And.intro checkAt canonAt
  next absent =>
    obtain ⟨checkAt, canonAt⟩ := atSuffix
    rw [List.drop_eq_nil_of_le (Nat.le_of_not_gt absent)] at checkAt canonAt
    simp only [Record.Effects.elements, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind'] at checkAt canonAt
    exact ⟨frame, checkAt, canonAt, frame.store.symm ▸ growth, atFinish left right check canon frame checkAt canonAt⟩
termination_by entries.length - index

theorem linkedStringMapBody {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (basePtr bytes : Nat)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (width : (core3 grow).memAddrType? left.store.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? left.store.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let area := layout site.destination.width (.record (mapEntryFields .string element))
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
    left.ctl = check.control (checkedCollectionTail site.destination site.inst entries area 0 route.output basePtr (.ok ()) >>= site.reply) →
    right.ctl = canon.control (canonicalCollectionTail site.destination site.inst entries area route.output basePtr mode >>= site.referenceReply) →
    LinkedStringMapBody profile ready base bindings older site element entries basePtr left right check canon := by
  intro area mode checkAt canonAt
  unfold LinkedStringMapBody
  intro publish checkTail canonTail
  refine linkedStringMapTraversal site linked element entries 0 nominal field fits left.store basePtr bytes width sized
    aligned bounds checkTail canonTail frame (frame.store ▸ Core3.Grows.refl _) embedder ?_ _ ?_
  · unfold LinkedStringMapAt
    simp only [List.drop_zero, Nat.zero_mul, Nat.add_zero]
    constructor
    · rw [checkAt]
      congr 1
      simp only [checkedCollectionTail, Prog.bind_eq, Prog.bind_assoc, checkTail, publish]
      congr 1
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok value => cases value; rfl
    · rw [canonAt]
      congr 1
      change Prog.bind (Prog.bind _ (fun _ => publish)) site.referenceReply = Prog.bind _ canonTail
      exact Prog.bind_assoc _ _ _
  · intro lhs rhs cursor peer paired lhsAt rhsAt
    let onChecked : route.output.Result → Session grow sig (Ret (core3 grow)) := fun result => site.reply (.ok result)
    have leftPublish : lhs.ctl = cursor.control (publish >>= onChecked) := by
      rw [lhsAt]
      simp only [checkTail, checkedSequenceNext, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind', onChecked]
    obtain ⟨store, result, labels, observed, leftWrites, rightWrites, tracks⟩ :=
      collection_descriptor_cut_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
        (reference := specDispatch ready (LiveDispatch.host bindings base)) (site.destination.context site.inst)
        site.destination.width route.output basePtr entries.length lhs rhs cursor peer onChecked site.referenceReply paired.store leftPublish rhsAt
    cases result with
    | error reason =>
      exact ⟨peer, .trapped reason, labels, labels, _, _, leftWrites.steps, rightWrites.steps, rfl, rfl, rfl, rfl, [], leafTrap observed⟩
    | ok descriptor =>
      exact ⟨peer, .returned descriptor, labels, labels, _, _, leftWrites.steps, rightWrites.steps, rfl, rfl,
        ⟨rfl, paired.pending, paired.results, paired.cancels, paired.blocked, paired.thread, paired.frames, paired.rest⟩,
        rfl, rfl, fun depth => (tracks descriptor rfl depth).1, fun depth => (tracks descriptor rfl depth).2, trivial⟩

theorem linkedStringMapPaths {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (element : Stored.TypeOf) (entries : List Field) (index basePtr : Nat)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {leftStart rightStart left right : Config (core3 grow) (HostState sig)}
    {check canon : Cursor (E := core3 grow) (HostState sig)} {seen callerLabels} {origin : CStore (core3 grow)}
    {offset : Nat}
    (caller : Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) callerLabels leftStart (.active 0 offset))
    (leading : ComparedSlots profile ready base bindings leftStart rightStart seen left right offset)
    (body : LinkedStringMapBody profile ready base bindings older site element entries basePtr left right check canon index origin) :
    LinkedStringMapPaths profile ready base bindings older site element entries index basePtr leftStart rightStart left right check canon seen offset := by
  unfold LinkedStringMapBody at body
  rw [LinkedStringMapTraversal] at body
  obtain ⟨⟨checkAt, canonAt⟩, stage⟩ := body
  rw [LinkedStringMapPaths]
  dsimp only
  split
  next present =>
    rw [dite_eq_left present] at stage
    unfold LinkedStringMapEntry at stage
    dsimp only at stage
    obtain ⟨key, value, selected, keyRun⟩ := stage checkAt canonAt
    obtain ⟨checkLabels, canonLabels, checkSeen, canonSeen, checkTracks, canonTracks, _, replay⟩ := keyRun
    have placed := CallbackPrefix.appendComparedSlots leading ⟨checkLabels, canonLabels, checkTracks, canonTracks, checkSeen, canonSeen⟩
    rw [List.append_nil] at placed
    refine ⟨key, value, selected, ⟨checkLabels, canonLabels, checkTracks, canonTracks, checkSeen, canonSeen⟩,
      CallbackPrefix.stringPaths ?_ placed replay⟩
    intro ptr lhs rhs cursor peer observed localCut accumulated
    obtain ⟨reached, outcome, lhsTrace, rhsTrace, leftFinal, rightFinal, leftRun, rightRun, same, traceSame, result⟩ := localCut
    let destination := site.destination
    let stride := (layout destination.width (.record (mapEntryFields .string element))).size
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) route.output
    let stop := MapReturnStop destination site.inst .string element entries route.output basePtr site.referenceReply
    have terminal (cut : CollectionSegment profile ready base bindings older lhs rhs cursor site.reply site.referenceReply 0 stop) :
        CollectionSegmentReplies profile ready base bindings older site leftStart rightStart stop offset := by
      obtain ⟨lhsPrefix, rhsPrefix, lhsTracks, rhsTracks, lhsSeen, rhsSeen⟩ := accumulated
      exact replies site caller (prependSegment lhsTracks rhsTracks (lhsSeen.trans rhsSeen.symm) cut)
    cases outcome with
    | trapped reason =>
      exact .inl (terminal ⟨reached, .trapped reason, lhsTrace, rhsTrace, leftFinal, rightFinal, leftRun, rightRun, same, traceSame, result⟩)
    | refused issue =>
      obtain ⟨pending, pendingAt, lhsAt, rhsAt, lhsTracks, rhsTracks⟩ := result
      have suffixOK : stop pending := by
        refine .inr ⟨entries.take index, entries.drop (index + 1), key.field, value, ?_, ?_⟩
        · calc
            entries = entries.take index ++ entries.drop index := (List.take_append_drop index entries).symm
            _ = _ := congrArg (entries.take index ++ ·)
              ((List.drop_eq_getElem_cons present).trans (congrArg (· :: entries.drop (index + 1)) selected))
        · rw [pendingAt]
          simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt present)]
          rfl
      exact .inl (terminal ⟨reached, .refused (.nested 0 issue), lhsTrace, rhsTrace, leftFinal, rightFinal,
        leftRun, rightRun, same, traceSame, pending, suffixOK, lhsAt, rhsAt, lhsTracks, rhsTracks⟩)
    | returned resultValue =>
      cases resultValue
      obtain ⟨_, _, _, lhsTracks, rhsTracks, tail⟩ := result
      let suffix := visible lhsTrace
      have continued : ComparedSlots profile ready base bindings lhs rhs suffix leftFinal rightFinal :=
        ⟨lhsTrace, rhsTrace, lhsTracks, rhsTracks, rfl, traceSame.symm⟩
      exact .inr ⟨leftFinal, rightFinal, reached, suffix, continued,
        linkedStringMapPaths site element entries (index + 1) basePtr caller (CallbackPrefix.appendComparedSlots accumulated continued) tail⟩
  next absent =>
    rw [dite_eq_right absent] at stage
    obtain ⟨checkLabels, canonLabels, checkTracks, canonTracks, checkSeen, canonSeen⟩ := leading
    exact replies site caller (prependSegment checkTracks canonTracks (checkSeen.trans canonSeen.symm)
      (by
        obtain ⟨peer, outcome, lhs, rhs, lhsEnd, rhsEnd, lhsRun, rhsRun, stores, labels, ending⟩ := stage.2.2.2.2
        refine ⟨peer, outcome, lhs, rhs, lhsEnd, rhsEnd, lhsRun, rhsRun, stores, labels, ?_⟩
        cases outcome with
        | returned _ | trapped _ => exact ending
        | refused _ =>
          obtain ⟨_, impossible, _⟩ := ending
          exact impossible.elim))
termination_by entries.length - index

theorem linkedStringMapReturn {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (pointer : Nat) (admitted : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {canonStart checked canonical : Config (core3 grow) (HostState sig)}
    {canonEntry check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace}
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let entryType : Stored.TypeOf := .record (mapEntryFields .string element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) output
    let first := checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        canonStart canonEntry second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    LinkedStringMapReturn profile ready base bindings older site element entries pointer checked canonical check := by
  intro entryType area output mode first second mark paired returned growth
  rw [field] at admitted
  obtain ⟨_, caller⟩ := collectionCaller site linked (.map .string element) entryType entries field admitted mark.checkedTrail
  have width := site.destination.check_width site.start.store linked.destination
  have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.map .string element) entryType
    entries output 0 pointer site.reply site.referenceReply mark paired returned width growth
  unfold LinkedStringMapReturn
  refine (rangeThenUnless site.destination site.inst entryType entries mode output 0 pointer site.reply site.referenceReply
    (MapReturnStop site.destination site.inst .string element entries output pointer site.referenceReply) _ (.inl rfl) ?_ cut).imp
    (replies site caller) id
  intro bytes left right canon reachedWidth sized aligned bounds frame checkAt canonAt lhs rhs checkRun canonRun seen
  exact .inr ⟨left, right, canon, lhs, rhs, _, checkRun, canonRun, seen, caller.append (checkRun 0),
    linkedStringMapBody site linked element entries nominal field fits pointer bytes reachedWidth sized aligned bounds frame embedder checkAt canonAt⟩

theorem linkedStringMapReturnPaths {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (pointer : Nat) (admitted : Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {canonStart checked canonical : Config (core3 grow) (HostState sig)}
    {canonEntry check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace}
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let entryType : Stored.TypeOf := .record (mapEntryFields .string element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) output
    let first := checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        canonStart canonEntry second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    LinkedStringMapReturnPaths profile ready base bindings older site element entries pointer checked canonical check := by
  intro entryType area output mode first second mark paired returned growth
  rcases linkedStringMapReturn site linked element entries nominal field fits pointer admitted embedder mark paired returned growth with
    terminal | ⟨left, right, canon, lhs, rhs, _, checkRun, canonRun, seen, _, body⟩
  · exact .inl terminal
  rw [field] at admitted
  obtain ⟨_, caller⟩ := collectionCaller site linked (.map .string element) entryType entries field admitted mark.checkedTrail
  have leading : ComparedSlots profile ready base bindings checked canonical (visible lhs) left right 1 :=
    ⟨lhs, rhs, checkRun, canonRun, rfl, seen.symm⟩
  exact .inr ⟨left, right, canon, visible lhs, leading, linkedStringMapPaths site element entries 0 pointer caller leading body⟩

private theorem referenceFrame {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {entered : Config (core3 grow) (HostState sig)}
    {body : Session grow sig (Ret (core3 grow))}
    (focus : (site.reference site.referenceReply).ctl = site.cursor.control body)
    (paired : HostFrame.Related.Paired older (site.reference site.referenceReply) entered) :
    ∃ peer : Cursor (E := core3 grow) (HostState sig),
      LinkedCallback.ChildFrameOver older site.checked entered site.cursor peer ∧ entered.ctl = peer.control body := by
  change ReturnFrame.Related.Paired older (HostFrame.replace (site.reference site.referenceReply) entered.host) entered at paired
  generalize entered.host = observer at paired
  let head : Config (core3 grow) (HostState sig) :=
    { site.start with host := observer, ctl := site.cursor.control body }
  have aligned : HostFrame.replace (site.reference site.referenceReply) observer = head := by
    change (site.reference site.referenceReply).ctl = _ at focus
    unfold PayloadRoot.Site.reference at focus
    unfold head HostFrame.replace PayloadRoot.Site.reference
    rw [show site.cursor.control (site.referenceProgram >>= site.referenceReply) = site.cursor.control body from focus]
  rw [aligned] at paired
  cases paired with
  | @mk rightControl rightSaved control saved =>
    change List.Forall₂ (ReturnFrame.Related.Active older)
      (⟨site.cursor.thread, .prog body, site.cursor.frames⟩ :: site.cursor.rest) rightControl at control
    cases control with
    | cons entry rest =>
      rename_i peerHead peerRest
      cases entry with
      | mk frames =>
        rename_i peerFrames
        exact ⟨⟨site.cursor.thread, peerFrames, peerRest⟩, ⟨rfl, rfl, rfl, rfl, saved, rfl, frames, rest⟩, rfl⟩

private theorem linkedCollection {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (type element : Stored.TypeOf) (entries : List Field)
    (field : site.field = .dynamic type element entries)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (prepared : Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    (visit : List Field → Nat → Nat → Finish grow sig)
    (children : CollectionVisitor site.destination site.inst type element entries 0 route.output site.reply site.referenceReply
      older site.checked.store (visit entries)) :
    LinkedCollectionBody profile ready base bindings older site type element incoming (fun _ entries pointer bytes _ => visit entries pointer bytes) := by
  obtain ⟨leading, entered, quiet, installed, framePaired, enteredHost⟩ :=
    LiveDispatch.entry_paired_tracks (profile := profile) (ready := ready) (base := base) site linked paired selected
  have bodyAt := site.reference_at linked site.referenceReply
  rw [field] at bodyAt
  obtain ⟨peer, frame, canonAt⟩ := referenceFrame site bodyAt framePaired
  have checkAt : site.checked.ctl = site.cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width (.dynamic type element entries) 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  have live : Record.prepare site.checked.store site.checked.host.writer (Field.listObjects entries) = .ok () := by
    change Record.prepare site.start.store site.start.host.writer (Field.listObjects entries) = .ok ()
    simpa only [field, Field.objects] using prepared
  have width := site.destination.check_width site.start.store linked.destination
  refine ⟨entries, leading, entered, peer, field, silent ?_, installed, enteredHost,
    collectionPathsFrom site.destination site.inst type element entries 0 route.output site.reply site.referenceReply frame
      (frame.store ▸ width) live checkAt canonAt embedder (visit entries) children (initialSlots site.checked entered)⟩
  intro label member
  have tau := List.all_eq_true.mp quiet label member
  cases label <;> simp_all

theorem linkedNominalListBody {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (depth : Nat) (element : Stored.TypeOf) (family : NominalListType depth element)
    (schema : sig.payload site.tag = .list element)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedNominalListBody profile ready base bindings older site depth element incoming)
      base := by
  refine site.parked_after_admission linked _ (fun _ _ prepared => ?_) base embedder
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  rw [schema] at matched
  obtain ⟨entries, field, shapes, emitted⟩ := listCompiled matched linked.emitted
  exact linkedCollection site linked (.list element) element entries field paired selected embedder prepared _
    (liveListVisitor site.destination site.inst element entries 0 route.output _ older site.checked.store site.checked.store (Core3.Grows.refl _)
      shapes (fun item member _ address => placedFieldOfRule (nominalListRule site.destination site.inst depth family item address
        (entries_match_of_mem shapes member) (emitted item member) embedder)) site.reply site.referenceReply _ (by intros; trivial))

theorem linkedMapListBody {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (key : WIT.KeyType) (keyData : LocalDataType (.prim key.toPrimitive))
    (depth : Nat) (element : Stored.TypeOf) (family : NominalListType depth element)
    (schema : sig.payload site.tag = .map key element)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedMapListBody profile ready base bindings older site key depth element incoming)
      base := by
  refine site.parked_after_admission linked _ (fun _ _ prepared => ?_) base embedder
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  rw [schema] at matched
  obtain ⟨entries, field, shapes⟩ := mapCompiled matched linked.emitted
  refine linkedCollection site linked (.map key element) (.record (mapEntryFields key element)) entries field paired selected
    embedder prepared _ (liveMapVisitor site.destination site.inst key element entries 0 route.output _ keyData older
      site.checked.store ?_ site.reply site.referenceReply _ (by intros; trivial))
  intro item member
  obtain ⟨payload, value, shape, layout, emitted⟩ := shapes item member
  exact ⟨payload, value, shape, layout.type_eq, fun _ address => nominalListRule site.destination site.inst depth family value address layout emitted embedder⟩

theorem linkedRecursiveCollectionBody {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {type : Stored.TypeOf} (family : RecursiveCollectionType type)
    (collection : CollectionRoot type) (schema : sig.payload site.tag = type)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedRecursiveCollectionBody profile ready base bindings older site incoming type)
      base := by
  refine site.parked_after_admission linked _ (fun fits _ prepared => ?_) base embedder
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  have source : CollectionSource site.destination site.field (sig.payload site.tag) :=
    ⟨matched, Record.preflightValue_value _ _ _ _ _ plan compiled ▸ fits, preflightAllocator site linked⟩
  rw [schema] at matched
  cases family with
  | leaf nominal => cases nominal <;> cases collection
  | data data => cases data <;> cases collection
  | string => cases collection
  | option => cases collection
  | result => cases collection
  | variant => cases collection
  | record => cases collection
  | tuple => cases collection
  | fixed => cases collection
  | @list element child =>
    obtain ⟨entries, field, shapes, emitted⟩ := listCompiled matched linked.emitted
    have rootPath : Field.Descendant site.field (.dynamic (.list element) element entries) := by
      rw [← field]; exact .self _
    exact linkedCollection site linked (.list element) element entries field paired selected embedder prepared _
      (liveListVisitor site.destination site.inst element entries 0 route.output _ older site.checked.store site.checked.store
        (Core3.Grows.refl _) shapes (fun item member _ address => collectionFieldRule site.destination site.inst child item address
          (entries_match_of_mem shapes member) (emitted item member) source (rootPath.trans (.dynamic member (.self _))) embedder)
        site.reply site.referenceReply _ (fun _ _ _ _ _ frame _ _ _ => frame))
  | @map key element child =>
    obtain ⟨entries, field, shapes⟩ := mapCompiled matched linked.emitted
    have rootPath : Field.Descendant site.field (.dynamic (.map key element) (.record (mapEntryFields key element)) entries) := by
      rw [← field]; exact .self _
    exact linkedCollection site linked (.map key element) (.record (mapEntryFields key element)) entries field paired selected
      embedder prepared _ (liveCompiledMapVisitor site.destination site.inst key element entries 0 route.output _ older
        site.checked.store source rootPath shapes (fun value ancestry layout emitted _ address =>
          collectionFieldRule site.destination site.inst child value address layout emitted source ancestry embedder)
        embedder site.reply site.referenceReply _ (fun _ _ _ _ _ frame _ _ _ => frame))

theorem linkedStringRecursiveMapBody {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (family : RecursiveCollectionType element)
    (schema : sig.payload site.tag = .map .string element)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedStringRecursiveMapBody profile ready base bindings older site element incoming)
      base :=
  linkedRecursiveCollectionBody site linked (.map family) True.intro schema paired selected embedder

private theorem liftLinkedCollection {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    {type element : Stored.TypeOf}
    {raw : Config (core3 grow) (HostState sig) → List Field → Nat → Nat → Finish grow sig}
    {visit : Config (core3 grow) (HostState sig) → List Field → Nat → Nat → TrailFinish grow sig}
    (body : LinkedCollectionBody profile ready base bindings older site type element incoming (fun entered entries ptr bytes _ =>
      raw entered entries ptr bytes))
    (next : ∀ entered entries pointer bytes observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings site.checked entered observed lhs rhs → lhs.store = rhs.store →
      raw entered entries pointer bytes lhs rhs cursor peer → visit entered entries pointer bytes observed lhs rhs cursor peer) :
    LinkedCollectionBody profile ready base bindings older site type element incoming visit := by
  obtain ⟨entries, leading, entered, peer, shape, quiet, entry, host, paths⟩ := body
  exact ⟨entries, leading, entered, peer, shape, quiet, entry, host,
    RecursiveTrails.allocationPaths (sink := .ignore) (fun _ _ _ _ _ _ _ _ _ _ => True.intro) True.intro
      (initialSlots site.checked entered) paths (next entered entries)⟩

private theorem publicRefusalCovers {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (entered : Config (core3 grow) (HostState sig)) :
    (publicRefusalSink profile ready base bindings site entered).Covers profile ready base bindings site.checked entered 0 := by
  unfold RefusalSink.Covers
  intro next admitted issue observed lhs rhs check control same tracks
  obtain ⟨reported, replyAt⟩ := admitted issue
  have checked := tracks
  obtain ⟨checkBody, canonBody, left, right, checkSeen, canonSeen⟩ := checked
  obtain ⟨segments, caller⟩ := site.reached_caller control (left 0)
  let reply := route.reply site.destination site.start.host.nextTicket (.error reported)
  have atReply : lhs.ctl = ⟨check.thread, .prog (do return .flat (← writeCompletion reply)),
        .core site.core site.resume :: segments⟩ :: check.rest := by
    simpa only [replyAt, Cursor.control, caller, PayloadRoot.Site.reply, reply] using control
  refine ⟨reported, replyAt, tracks, same, segments, checkBody, canonBody, checkSeen, canonSeen,
    fun _ place => Plain.give_completion_trail reply place atReply, ?_, ?_⟩
  · exact appendReplyTrack left (fun place => Plain.give_completion_trail reply place atReply)
  · simpa only [Nat.add_zero] using right

private theorem rootVisitorAdmits {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (entered : Config (core3 grow) (HostState sig)) :
    (publicRefusalSink profile ready base bindings site entered).admits (fun issue => site.reply (.error (.nested 0 issue))) :=
  fun issue => ⟨.nested 0 issue, rfl⟩

theorem linkedCollectionRejoinPaths {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {type : Stored.TypeOf} (family : RecursiveCollectionType type)
    (collection : CollectionRoot type) (schema : sig.payload site.tag = type)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedCollectionRejoinPaths profile ready base bindings older site incoming type) base := by
  have cut := linkedRecursiveCollectionBody (profile := profile) (ready := ready) site linked
    family collection schema paired selected embedder
  cases cut with
  | refused issue quiet run => exact .refused issue quiet run
  | placementTrap reason count verdict run => exact .placementTrap reason count verdict run
  | placed silent verdict prepared path body =>
    refine .placed silent verdict prepared path ?_
    cases family with
    | leaf nominal => cases nominal <;> cases collection
    | data data => cases data <;> cases collection
    | string | fixed | option | result | variant | record | tuple => cases collection
    | list child =>
      refine liftLinkedCollection body ?_
      intro entered entries pointer bytes observed lhs rhs cursor peer tracks same elements
      exact CallbackPrefix.liveElementsPathsFrom (RecursiveTrails.fieldPaths (publicRefusalCovers site entered) child)
        tracks same elements (rootVisitorAdmits site entered)
        (fun _ _ _ _ _ terminal _ publish => rejoinPublished site (.done _ _) terminal publish)
    | map child =>
      refine liftLinkedCollection body ?_
      intro entered entries pointer bytes observed lhs rhs cursor peer tracks same elements
      exact RecursiveTrails.mapElementsPaths (RecursiveTrails.fieldPaths (publicRefusalCovers site entered) child)
        tracks same elements (rootVisitorAdmits site entered)
        (fun _ _ _ _ _ terminal _ publish => rejoinPublished site (.done _ _) terminal publish)

theorem linkedStringRejoinPaths {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (schema : sig.payload site.tag = .prim .string)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedStringRejoinPaths profile ready base bindings older site incoming) base := by
  refine site.parked_after_admission linked _ (fun fits placed _ => ?_) base embedder
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  have source : CollectionSource site.destination site.field (sig.payload site.tag) :=
    ⟨matched, Record.preflightValue_value _ _ _ _ _ plan compiled ▸ fits, preflightAllocator site linked⟩
  obtain ⟨str, field⟩ := stringCompiled (schema ▸ matched) linked.emitted
  have descent : site.field.Descendant str.field := by rw [field]; exact .self _
  obtain ⟨leading, entered, quiet, installed, framePaired, enteredHost⟩ :=
    LiveDispatch.entry_paired_tracks (profile := profile) (ready := ready) (base := base) site linked paired selected
  obtain ⟨peer, frame, canonAt⟩ := referenceFrame site (site.reference_at linked site.referenceReply) framePaired
  have width := site.destination.check_width site.start.store linked.destination
  have checkAt : site.checked.ctl = site.cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width str.field 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  let finish : Nat → Finish grow sig := fun _ => LiveValueCommit profile ready base bindings route.output site.reply site.referenceReply
    (fun _ => LinkedCallback.ChildFrameOver older)
  rw [field] at canonAt
  have body := stringValueThen (profile := profile) (ready := ready) (base := base) (origin := site.checked.store)
    site.destination site.inst str route.output source descent embedder frame (Core3.Grows.refl _) width (schema ▸ placed)
    checkAt canonAt (finish := finish) (fun pointer _ _ _ _ related _ lhsAt rhsAt =>
      stringValueCommit (site.destination.context site.inst) site.destination.width route.output _ pointer related lhsAt rhsAt)
  refine ⟨str, leading, entered, peer, field, silent ?_, installed, enteredHost,
    CallbackPrefix.stringValuePaths (initialSlots site.checked entered) body
      (fun _ _ _ _ _ _ committed tracks => rejoinPublished site (.done _ _) tracks committed)⟩
  intro label member
  have tau := List.all_eq_true.mp quiet label member
  cases label <;> simp_all

private theorem rejoinReady {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {entered left right : Config (core3 grow) (HostState sig)} {observed : Trace grow sig}
    {check canon : Cursor (E := core3 grow) (HostState sig)}
    (leading : ComparedSlots profile ready base bindings site.checked entered observed left right)
    (value : route.output.Result) (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (checkAt : left.ctl = check.control (site.reply (.ok value)))
    (canonAt : right.ctl = canon.control (site.referenceReply value))
    {afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop}
    (next : ∀ first second, HostFrame.Related.Paired older first second → afterReturn first second) :
    CollectionSegmentReplies profile ready base bindings older site site.checked entered (fun _ => False) 0 afterReturn := by
  obtain ⟨lhs, rhs, checked, canonical, seenLeft, seenRight⟩ := leading
  have terminal : CollectionSegment profile ready base bindings older left right check site.reply site.referenceReply 0
      (fun _ => False) :=
    ⟨canon, .returned value, [], [], left, right, .refl _, .refl _, frame.store, rfl, frame, checkAt, canonAt,
      fun _ => .done _ _, fun _ => .done _ _, trivial⟩
  exact replies site (.done _ _) (prependSegment checked canonical (seenLeft.trans seenRight.symm) terminal) afterReturn next

theorem linkedMemoryRejoinPaths {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True)
    (next : ∀ left right, HostFrame.Related.Paired older left right → afterReturn left right := by intros; trivial) :
    PayloadRoot.Cut site profile ready bindings (LinkedMemoryRejoinPaths profile ready base bindings older site incoming afterReturn) base := by
  refine site.parked_after_admission linked _ (fun fits placed _ => ?_) base embedder
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  have source : CollectionSource site.destination site.field (sig.payload site.tag) :=
    ⟨matched, Record.preflightValue_value _ _ _ _ _ plan compiled ▸ fits, preflightAllocator site linked⟩
  obtain ⟨leading, entered, quiet, installed, framePaired, enteredHost⟩ :=
    LiveDispatch.entry_paired_tracks (profile := profile) (ready := ready) (base := base) site linked paired selected
  obtain ⟨peer, frame, canonAt⟩ := referenceFrame site (site.reference_at linked site.referenceReply) framePaired
  have width := site.destination.check_width site.start.store linked.destination
  have position : placement site.destination site.checked.store (layout site.destination.width site.field.type) (flatNat pointer) = .ok () :=
    matched.type_eq.symm ▸ placed
  have compiledBody := collectionFieldRule (profile := profile) (ready := ready) (base := base) (older := older)
    (origin := site.checked.store) site.destination site.inst family site.field (flatNat pointer)
    matched linked.emitted source (.self _) embedder
  have body := compiledBody 0 site.reply site.referenceReply site.checked entered site.cursor peer frame
    (Core3.Grows.refl _) width position rfl canonAt (MemoryRootFinish older site)
    (fun _ _ _ _ linkedFrame _ checkAt canonicalAt => ⟨linkedFrame, checkAt, canonicalAt⟩)
  refine ⟨leading, entered, peer, silent ?_, installed, enteredHost, ?_⟩
  · intro label member
    have tau := List.all_eq_true.mp quiet label member
    cases label <;> simp_all
  · exact RecursiveTrails.fieldPaths (publicRefusalCovers site entered) family site.field 0 (flatNat pointer) _ _ _ _
      site.reply site.referenceReply _ _ [] body (initialSlots site.checked entered) frame.store
      (fun issue => ⟨issue, rfl⟩) (fun _ _ _ _ _ tracks _ ⟨paired, checkAt, canonAt⟩ =>
        rejoinReady site tracks () paired checkAt canonAt next)

theorem linkedFlatAggregateRejoinPaths {type : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat type))
    (linked : site.Linked bindings) (family : RecursiveCollectionType (sig.payload site.tag))
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (afterReturn : Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop := fun _ _ => True)
    (next : ∀ left right, HostFrame.Related.Paired older left right → afterReturn left right := by intros; trivial) :
    PayloadRoot.Cut site profile ready bindings (LinkedFlatAggregateRejoinPaths profile ready base bindings older site incoming afterReturn) base := by
  refine site.parked_after_admission linked _ (fun fits _ _ => ?_) base embedder
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  have source : CollectionSource site.destination site.field (sig.payload site.tag) :=
    ⟨matched, Record.preflightValue_value _ _ _ _ _ plan compiled ▸ fits, preflightAllocator site linked⟩
  obtain ⟨leading, entered, quiet, installed, framePaired, enteredHost⟩ :=
    LiveDispatch.entry_paired_tracks (profile := profile) (ready := ready) (base := base) site linked paired selected
  obtain ⟨peer, frame, canonAt⟩ := referenceFrame site (site.reference_at linked site.referenceReply) framePaired
  have width := site.destination.check_width site.start.store linked.destination
  have traversal := flatCompiledField (profile := profile) (ready := ready) (base := base) (bindings := bindings)
    (origin := site.checked.store) (older := older) site.destination site.inst
    family site.field matched linked.emitted source (.self _) embedder width (publicRefusalCovers site entered)
  refine ⟨leading, entered, peer, silent ?_, installed, enteredHost, ?_⟩
  · intro label member
    have tau := List.all_eq_true.mp quiet label member
    cases label <;> simp_all
  · exact traversal 0 site.reply site.referenceReply _ [] site.checked entered site.cursor peer frame (Core3.Grows.refl _)
      (initialSlots site.checked entered) (fun issue => ⟨issue, rfl⟩) rfl canonAt
      (fun words _ _ _ _ _ paired _ tracks lhs rhs => rejoinReady site tracks words paired lhs rhs next)

private theorem collectionReturnFailure {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (type element : Stored.TypeOf) (entries : List Field) (pointer : Nat)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)} {check : Cursor (E := core3 grow) (HostState sig)}
    {leading : Trace grow sig}
    (caller : Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) leading checked (.active 0 1))
    (range : CollectionRangeCut profile ready base bindings older checked canonical check site.destination
      (layout site.destination.width element) entries.length pointer (Field.listObjects entries)
      (fun addr verdict => checkedCollectionTail site.destination site.inst entries (layout site.destination.width element)
        0 route.output addr verdict >>= site.reply)
      (fun addr => canonicalCollectionTail site.destination site.inst entries (layout site.destination.width element)
        route.output addr (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply)) :
    CollectionReturnFailure profile ready base bindings site type element entries pointer checked canonical check := by
  have ⟨_, bytes, _, sized, frame, verdict⟩ := range
  refine ⟨frame.store, bytes, sized, ?_⟩
  by_cases aligned : pointer = alignTo pointer (layout site.destination.width element).alignment
  · simp only [ite_eq_right (not_not_intro aligned)] at verdict ⊢
    by_cases bounds : pointer + entries.length * (layout site.destination.width element).size ≤ bytes
    · simp only [ite_eq_left bounds]
      intro issue refused
      obtain ⟨canon, lhs, rhs, segments, checkQuiet, canonQuiet, checkRun, canonRun⟩ :=
        refusalReply site type element entries 0 pointer bytes range caller sized aligned bounds refused
      exact ⟨canon, lhs, rhs, segments, silent checkQuiet, silent canonQuiet, checkRun, canonRun⟩
    · simp only [ite_eq_right bounds] at verdict ⊢
      obtain ⟨⟨leftCount, left⟩, ⟨rightCount, right⟩⟩ := verdict
      exact ⟨leftCount, rightCount, left, right⟩
  · simp only [ite_eq_left aligned] at verdict ⊢
    obtain ⟨⟨leftCount, left⟩, ⟨rightCount, right⟩⟩ := verdict
    exact ⟨leftCount, rightCount, left, right⟩

private theorem liftLinkedCollectionFailures {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {type element : Stored.TypeOf}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    {visit : Config (core3 grow) (HostState sig) → List Field → Nat → Nat → TrailFinish grow sig}
    (prepared : Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    (body : LinkedCollectionBody profile ready base bindings older site type element incoming visit) :
    LinkedCollectionReturnFailures profile ready base bindings older site incoming type element := by
  obtain ⟨entries, leading, entered, peer, field, quiet, entry, _, paths⟩ := body
  refine ⟨entries, leading, entered, peer, field, quiet, entry, ?_⟩
  intro area mode first second checkedEntry canonEntry seen checked callback
  obtain ⟨lhs, rhs, canonical, mark, marked, _, compared, returns⟩ := paths callback
  refine ⟨lhs, rhs, canonical, mark, marked, ?_, ?_⟩
  · simpa only [List.nil_append] using CallbackPrefix.allocatorSteps compared
  intro pointer cursor active returned
  obtain ⟨range, _, _⟩ := returns pointer cursor active returned
  have initial : Record.prepare site.checked.store site.checked.host.writer (Field.listObjects entries) = .ok () := by
    change Record.prepare site.start.store site.start.host.writer (Field.listObjects entries) = .ok ()
    simpa only [field, Field.objects] using prepared
  have trail := marked.checkedTrail
  rw [active] at trail
  obtain ⟨_, caller⟩ := collectionCaller site linked type element entries field initial trail
  exact collectionReturnFailure site type element entries pointer caller range

theorem linkedCollectionReturnFailures {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) {type : Stored.TypeOf} (family : RecursiveCollectionType type)
    (collection : CollectionRoot type) (schema : sig.payload site.tag = type)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (match type with
      | .list element => LinkedCollectionReturnFailures profile ready base bindings older site incoming type element
      | .map key element => LinkedCollectionReturnFailures profile ready base bindings older site incoming type
          (.record (mapEntryFields key element))
      | _ => False) base := by
  have cut := linkedRecursiveCollectionBody (profile := profile) (ready := ready) site linked
    family collection schema paired selected embedder
  cases cut with
  | refused issue quiet run => exact .refused issue quiet run
  | placementTrap reason count verdict run => exact .placementTrap reason count verdict run
  | placed quiet verdict prepared path body =>
    refine .placed quiet verdict prepared path ?_
    cases type <;> first | exact liftLinkedCollectionFailures site linked prepared body | contradiction

theorem linkedStringMapDispatch {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older site.start incoming)
    (selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    PayloadRoot.Cut site profile ready bindings (LinkedStringMapDispatch profile ready base bindings older site element entries incoming)
      base := by
  refine site.parked_after_admission linked _ (fun fits _ prepared => ?_) base embedder
  obtain ⟨leading, entered, quiet, installed, framePaired, enteredHost⟩ :=
    LiveDispatch.entry_paired (profile := profile) (ready := ready) (base := base) site linked paired selected
  have bodyAt := site.reference_at linked site.referenceReply
  rw [field] at bodyAt
  obtain ⟨peer, frame, canonAt⟩ := referenceFrame site bodyAt framePaired
  have checkAt : site.checked.ctl = site.cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width
      (.dynamic (.map .string element) (.record (mapEntryFields .string element)) entries) 0 route.output >>= site.reply) := by
    simp only [PayloadRoot.Site.checked, PayloadRoot.Site.withBody, field]
  have width := site.destination.check_width site.start.store linked.destination
  have preparedAt : Record.prepare site.checked.store site.checked.host.writer (Field.listObjects entries) = .ok () := by
    change Record.prepare site.start.store site.start.host.writer (Field.listObjects entries) = .ok ()
    simpa only [field, Field.objects] using prepared
  have leadingSilent : visible leading = [] := by
    apply silent
    intro label member
    have tau := List.all_eq_true.mp quiet label member
    cases label <;> simp_all
  unfold LinkedStringMapDispatch
  refine ⟨leading, entered, peer, leadingSilent, installed, enteredHost, ?_⟩
  intro rightEntry seen checked path
  obtain ⟨lhs, rhs, reached, mark, left, right, live, seenLeft, seenRight, growth, _, _, tracked⟩ :=
    CallbackPrefix.collectionPrefix (profile := profile) (ready := ready) site.destination site.inst (.map .string element)
      (.record (mapEntryFields .string element)) entries route.output 0 site.reply site.referenceReply frame
      (frame.store ▸ width) preparedAt checkAt canonAt embedder path
  have same : checked.store = reached.store := by
    change ReturnFrame.Related.Paired _ (HostFrame.replace checked reached.host) reached at live
    generalize reached.host = observer at live
    cases live
    rfl
  refine ⟨lhs, rhs, reached, mark, tracked, live, ⟨_, _, left, appendRun installed right, ?_, ?_, same⟩, ?_⟩
  · rw [appendVisible, silent (by simp), List.nil_append, seenLeft]
  · rw [appendVisible, appendVisible, leadingSilent, silent (by simp), List.nil_append, List.nil_append, seenRight]
  · intro pointer check top returned
    subst mark
    exact linkedStringMapReturnPaths site linked element entries nominal field fits pointer prepared embedder tracked live returned growth

theorem nominalMapReplies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (keyData : LocalDataType (.prim key.toPrimitive)) (nominal : NominalElement element)
    (field : site.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries) (pointer : Nat)
    (admitted : Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map key element) output
    let first := checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionSegmentReplies profile ready base bindings older site checked canonical
      (MapReturnStop site.destination site.inst key element entries output pointer site.referenceReply) := by
  intro entryType area output mode first second mark paired returned growth
  obtain ⟨objects, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ objects compiled
  have emitted := Record.preflightValue_emitted _ _ _ _ _ objects compiled
  rw [field] at matched emitted admitted
  have children := mapEntries matched
  cases emitted with
  | map shapes emitted =>
    have shape : ∀ item ∈ entries, ∃ (keyPayload : Stored.Payload (.prim key.toPrimitive)) (value : Field),
        item = .aggregate entryType [.data (.prim key.toPrimitive) keyPayload, value] ∧
          value.LayoutMatches element ∧ value.Emitted := by
      intro item member
      have layout := entries_match_of_mem children member
      obtain ⟨keyPayload, value, rfl⟩ := shapes item member
      exact ⟨keyPayload, value, rfl, mapValueLayout layout, emitted keyPayload value member⟩
    obtain ⟨_, caller⟩ := collectionCaller site linked (.map key element) entryType entries field admitted mark.checkedTrail
    have width := site.destination.check_width site.start.store linked.destination
    have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.map key element) entryType
      entries output 0 pointer site.reply site.referenceReply mark paired returned width growth
    refine replies site caller (rangeThen site.destination site.inst entryType entries mode output 0 pointer
      site.reply site.referenceReply (MapReturnStop site.destination site.inst key element entries output pointer
        site.referenceReply) (.inl rfl) ?_ cut)
    intro bytes left right canon reachedWidth sized aligned bounds frame checkAt canonAt
    obtain ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, leftRun, rightRun, same, seen, status⟩ :=
      finishElements site.destination site.inst entries area mode output 0 pointer site.reply site.referenceReply checkAt canonAt
        (MapValueStop site.destination site.inst key element mode entries area.size pointer)
        (fun checkTail canonTail lhs rhs => by
          have visit := nominalMapElements (profile := profile) (ready := ready) (base := base) (bindings := bindings)
            site.destination site.inst key element output keyData nominal left.store pointer bytes entries.length reachedWidth sized aligned bounds
            entries 0 (by simp) shape checkTail canonTail frame (frame.store ▸ Core3.Grows.refl _)
          simp only [Nat.zero_mul, Nat.add_zero] at visit
          exact visit lhs rhs)
    refine ⟨reached, outcome, lhs, rhs, finalLeft, finalRight, leftRun, rightRun, same, seen, ?_⟩
    cases outcome with
    | returned _ | trapped _ => exact status
    | refused _ =>
      obtain ⟨stop, witness, tail⟩ := status
      exact ⟨stop, .inr witness, tail⟩

theorem localMapReplies {outputPointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory outputPointer))
    (linked : site.Linked bindings) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (keyData : LocalDataType (.prim key.toPrimitive)) (valueData : LocalDataType element)
    (field : site.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries) (pointer : Nat)
    {older wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let area := layout site.destination.width entryType
    let mode := CanonicalTree.EntryMode.memoryMap site.destination.width key element
    let output := (GiveEffectRoute.memory outputPointer).output
    let first := checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionReplies profile ready base bindings older site checked canonical
      (canonicalCollectionTail site.destination site.inst entries area output pointer mode >>= site.referenceReply) := by
  intro entryType area mode output first second mark paired returned growth
  obtain ⟨objects, compiled⟩ := linked.compiled
  have matched := Stored.OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ objects compiled
  have emitted := Stored.OwnedMemory.Claims.Record.preflightValue_emitted _ _ _ _ _ objects compiled
  rw [field] at matched emitted
  have children := mapEntries matched
  have prepared : Stored.OwnedMemory.Claims.Record.prepare site.checked.store site.checked.host.writer
      (Field.listObjects entries) = .ok () := by rw [local_data_map_objects valueData children emitted]; rfl
  obtain ⟨_, caller⟩ := collectionCaller site linked (.map key element) entryType entries field prepared mark.checkedTrail
  have width := site.destination.check_width site.start.store linked.destination
  have cut := collectionRange (profile := profile) (ready := ready) site.destination site.inst (.map key element) entryType
    entries output 0 pointer site.reply site.referenceReply mark paired returned width growth
  exact replies site caller (localTail site.destination site.inst entryType entries mode output 0 pointer site.reply site.referenceReply
    (fun bytes left right canon reachedWidth sized aligned bounds same thread checkAt rightAt =>
      local_map_collection_tail site.destination site.inst key element keyData valueData entries children emitted pointer bytes 0
        (flatNat outputPointer) left right reachedWidth sized aligned bounds same check canon thread site.reply site.referenceReply
        checkAt rightAt) cut)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange
