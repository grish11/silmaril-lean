module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch ComponentCall.Delivery.FiniteSession
open ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {seen : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

private theorem append {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before middle after : Config (core3 grow) (HostState sig)} {leading trailing}
    (front : Steps profile ready dispatch before leading middle) (back : Steps profile ready dispatch middle trailing after) :
    Steps profile ready dispatch before (leading ++ trailing) after := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

private theorem invisible {labels : Trace grow sig} (silent : labels.all (· matches .tau) = true) :
    PayloadPrefix.visible labels = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro label member
  have tau := List.all_eq_true.mp silent label member
  cases label <;> simp_all

theorem visibleLeaf {Result : Type} {outcome : Except TrapReason Result} {labels : Trace grow sig}
    (classified : LocalLeafLabels outcome labels) :
    PayloadPrefix.visible labels = (match outcome with | .ok _ => [] | .error reason => [.trap reason]) := by
  cases outcome with
  | ok _ =>
    apply List.filter_eq_nil_iff.mpr
    intro label member
    have tau := List.all_eq_true.mp classified label member
    cases label <;> simp_all
  | error reason =>
    obtain ⟨count, rfl⟩ := classified
    change PayloadPrefix.visible (List.replicate count .tau ++ [.trap reason]) = [.trap reason]
    rw [show PayloadPrefix.visible (List.replicate count .tau ++ [.trap reason] : Trace grow sig) =
      PayloadPrefix.visible (List.replicate count .tau : Trace grow sig) ++ PayloadPrefix.visible ([.trap reason] : Trace grow sig)
      from List.filter_append .., invisible (by simp)]
    rfl

private theorem noAssignmentPeer (paired : HostFrame.Related.Paired older start incoming)
    (closed : NoHostAssignment start) : NoHostAssignment incoming := by
  intro thread value next frames rest focused
  change ReturnFrame.Related.Paired older (HostFrame.replace start incoming.host) incoming at paired
  generalize incoming.host = observer at paired
  cases paired with
  | @mk active _ control _ =>
    change List.Forall₂ (ReturnFrame.Related.Active older) start.ctl _ at control
    change active = _ at focused
    rw [focused] at control
    generalize leftFocus : start.ctl = leftControl at control
    cases control with
    | cons head _ =>
      cases head
      exact closed _ _ _ _ _ leftFocus

private theorem stepHost {other : Config (core3 grow) (HostState sig)} {label}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (closed : NoHostAssignment start) (step : Step profile ready dispatch start label other) : other.host = start.host := by
  cases step <;> try rfl
  case hostDone => unfold StepDefs.hostFinish; split <;> rfl
  case hostSet focused => exact (closed _ _ _ _ _ focused).elim
  case emit => rename_i observation _ _ _ _; cases observation <;> rfl

theorem coreInternal {protectedReturn thread core next frames rest store coreNext}
    (focused : start.ctl = ⟨thread, .core core next, frames⟩ :: rest)
    (running : (core3 grow).status start.store.core core = .running ∨ (core3 grow).status start.store.core core = .stuck)
    (executed : (core3 grow).Internal (start.store.core, core) (store, coreNext))
    (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn
      { start with store := { start.store with core := store }, ctl := ⟨thread, .core coreNext next, frames⟩ :: rest } seen finish) :
    ClosedCallbackPrefix bindings profile ready base protectedReturn start (.core :: seen) finish := by
  refine .step ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ ?_ (.coreInternal focused running executed) tail
  · intros; simp [focused]
  · intros; simp [focused]
  · intro _ _ _ _ _ other
    rw [focused] at other
    cases other
  · intro _ _ _ _ _ _ _ other calling
    rw [focused] at other
    cases other
    rcases running with status | status <;> rw [status] at calling <;> contradiction
  · intro _ _ _ _ _; simp [focused]
  · simp [CoreUpdateGrows, focused]

private theorem unchangedTrail {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before after : Config (core3 grow) (HostState sig)} {trace}
    (tracks : ∀ place, Prefix profile ready dispatch before place trace after place) (mark : Option Location) :
    Trail profile ready dispatch before mark trace after mark := by
  cases mark with
  | none => exact Trail.absent (prefix_survives (tracks (.active 0 0))).1
  | some place => exact (tracks place).toTrail

theorem replayMarked {protectedReturn} {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (path : ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (covers : ∀ first second, wider first second → protectedReturn first)
    (paired : HostFrame.Related.Paired wider start incoming) {mark : Option Location}
    (outside : Outside older (segmentStorage start) (segmentStorage incoming) mark) :
    ∃ checkedLabels canonLabels reached finalMark,
      Steps profile ready (specDispatch ready base) start checkedLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonLabels reached ∧
      HostFrame.Related.Paired wider finish reached ∧
      PayloadPrefix.visible checkedLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted ∧
      Outside older (segmentStorage finish) (segmentStorage reached) finalMark ∧
      Trail profile ready (specDispatch ready base) start mark checkedLabels finish finalMark ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming mark canonLabels reached finalMark ∧
      CoupledOccurrencePaths profile ready base bindings start incoming checkedLabels canonLabels finish reached := by
  induction path generalizing incoming mark with
  | done => exact ⟨[], [], incoming, mark, .refl _, .refl _, paired, rfl, rfl, .refl _, rfl, rfl, outside, .done _ _, .done _ _,
      fun cursor => ⟨cursor, .done _ _, .done _ _⟩⟩
  | @step current next last label rest interior unchanged noAssignment grows run _ ih =>
    have live : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) current label next := by
      rcases LiveDispatch.classify_step (bindings := bindings) run with live | install
      · exact live
      · cases install with
        | direct focused overlaid => exact (overlaid (unchanged.direct focused)).elim
        | core focused calling overlaid => exact (overlaid (unchanged.core focused calling)).elim
    obtain ⟨peer, replay, aligned⟩ := HostFrame.Related.interior_step covers paired interior grows live
    have peerStep : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming label peer := by
      cases replay with
      | cons _ step tail => cases tail; exact step
    have edit := pair_edit paired label
    have nextOutside : Outside older (segmentStorage next) (segmentStorage peer) (mark.bind (transitionEdit current label).follow) := by
      rw [step_edit run, step_edit peerStep, ← edit]
      exact outside_edit outside _
    obtain ⟨checkedLabels, canonLabels, reached, finalMark, checked, canonical, final, checkSeen, canonSeen, growth,
      checkRoots, canonRoots, finalOutside, checkTrail, canonTrail, movement⟩ := ih aligned nextOutside
    refine ⟨_, _, reached, finalMark, .cons run checked, .cons peerStep canonical, final,
      (List.filter_append [_] checkedLabels).trans (congrArg (_ ++ ·) checkSeen),
      (List.filter_append [_] canonLabels).trans (congrArg (_ ++ ·) canonSeen),
      (CoreGrowthSteps.cons grows run (.refl _)).grows.trans growth,
      checkRoots.trans (congrArg (·.writer.accepted) (stepHost noAssignment run)),
      canonRoots.trans (congrArg (·.writer.accepted) (stepHost (noAssignmentPeer paired noAssignment) peerStep)),
      finalOutside, .step run checkTrail, .step peerStep (by rwa [← edit]), ?_⟩
    intro cursor
    obtain ⟨target, left, right⟩ := movement (cursor.bind (transitionEdit current label).follow)
    exact ⟨target, .step run left, .step peerStep (edit ▸ right)⟩
  | confinedGive callout _ ih =>
    obtain ⟨count, checked, _, _, checkedSlots⟩ := Plain.parked_closed_give_steps bindings callout.name callout.type callout.args
      callout.inst callout.destination callout.schema _ callout.thread profile ready callout.parked callout.calling
      callout.linked callout.caller callout.live callout.closed base embedder
    obtain ⟨leading, peer, silent, canonical, aligned, host, canonSlots⟩ :=
      LiveDispatch.closed_give_paired (profile := profile) (ready := ready) (base := base) callout paired
    have nextOutside : Outside older (segmentStorage callout.resume) (segmentStorage peer) mark :=
      fun place offMark first second leftAt rightAt => outside place offMark first second
        ((prefix_survives (checkedSlots place)).2.symm.trans leftAt)
        ((prefix_survives (canonSlots place)).2.symm.trans rightAt)
    obtain ⟨checkLabels, canonLabels, reached, finalMark, checkTail, canonTail, final, checkSeen, canonSeen, growth,
      checkRoots, canonRoots, finalOutside, checkTrail, canonTrail, movement⟩ := ih aligned nextOutside
    have tau : (List.replicate count (.tau : Label (core3 grow) (HostState sig))).all (· matches .tau) = true := by
      apply List.all_eq_true.mpr
      intro label member
      rw [List.eq_of_mem_replicate member]
    refine ⟨_, _, reached, finalMark, append checked.steps checkTail, append canonical canonTail, final,
      (List.filter_append _ checkLabels).trans (by rw [← PayloadPrefix.visible, invisible tau, List.nil_append]; exact checkSeen),
      (List.filter_append _ canonLabels).trans (by rw [← PayloadPrefix.visible, invisible silent, List.nil_append]; exact canonSeen),
      growth, checkRoots, canonRoots.trans (congrArg (·.writer.accepted) host), finalOutside,
      (unchangedTrail checkedSlots mark).append checkTrail, (unchangedTrail canonSlots mark).append canonTrail, ?_⟩
    intro cursor
    obtain ⟨target, left, right⟩ := movement cursor
    exact ⟨target, (unchangedTrail checkedSlots cursor).append left, (unchangedTrail canonSlots cursor).append right⟩
  | @syncReady current _ _ task inst thread frames rest focused agrees _ ih =>
    let residual := syncLiftCandidates (E := core3 grow) (σ := HostState sig) task
      (current.store.instCandidates (ready current.host) inst)
    obtain ⟨peerFrames, peerRest, atPeer, aligned⟩ := paired.retarget focused (.prog residual) current.host incoming.host
    have candidates := HostFrame.instCandidates_eq current.store inst (ready current.host) (ready incoming.host)
      (fun entry live blockedThread member suspended found blocked query condition =>
        agrees entry live blockedThread member suspended found blocked query condition incoming.host)
    have peerStep : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
        { incoming with ctl := ⟨thread, .prog residual, peerFrames⟩ :: peerRest } := by
      unfold residual
      rw [candidates]
      exact .hostGet atPeer
    have nextOutside : Outside older
        (segmentStorage { current with ctl := ⟨thread, .prog residual, frames⟩ :: rest })
        (segmentStorage { incoming with ctl := ⟨thread, .prog residual, peerFrames⟩ :: peerRest }) mark := by
      simpa only [segmentStorage, focused, atPeer, List.map_cons, Activation.segs] using outside
    obtain ⟨_, _, reached, finalMark, checked, canonical, final, checkSeen, canonSeen, growth,
      checkRoots, canonRoots, finalOutside, checkTrail, canonTrail, movement⟩ := ih aligned nextOutside
    have unchanged (cursor : Option Location) : cursor.bind (Edit.same (E := core3 grow) (Host := HostState sig)).follow = cursor := by
      cases cursor with
      | none => rfl
      | some place => cases place <;> rfl
    refine ⟨_, _, reached, finalMark, .cons (.hostGet focused) checked, .cons peerStep canonical, final,
      checkSeen, canonSeen, growth, checkRoots, canonRoots, finalOutside, .step (.hostGet focused) ?_, .step peerStep ?_, ?_⟩
    · rw [transitionEdit, focused]
      exact (unchanged mark).symm ▸ checkTrail
    · rw [transitionEdit, atPeer]
      exact (unchanged mark).symm ▸ canonTrail
    · intro cursor
      obtain ⟨target, left, right⟩ := movement cursor
      refine ⟨target, .step (.hostGet focused) ?_, .step peerStep ?_⟩
      · rw [transitionEdit, focused]
        exact (unchanged cursor).symm ▸ left
      · rw [transitionEdit, atPeer]
        exact (unchanged cursor).symm ▸ right

theorem replay {protectedReturn}
    (path : ClosedCallbackPrefix bindings profile ready base protectedReturn start seen finish)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (covers : ∀ first second, older first second → protectedReturn first)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ checkedLabels canonLabels reached,
      Steps profile ready (specDispatch ready base) start checkedLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonLabels reached ∧
      HostFrame.Related.Paired older finish reached ∧
      PayloadPrefix.visible checkedLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted := by
  obtain ⟨checkedLabels, canonLabels, reached, _, checked, canonical, final, checkSeen, canonSeen, growth,
    checkRoots, canonRoots, _, _, _, _⟩ := replayMarked path embedder covers paired
      (paired_outside (left := HostFrame.replace start incoming.host) paired)
  exact ⟨checkedLabels, canonLabels, reached, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots⟩

theorem stringReallocPrefix (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (path : ClosedCallbackPrefix bindings profile ready base
      (fun resume => (∃ peer, older resume peer) ∨ resume = PayloadPrefix.stringPlanResume cx steps checkNext)
      (LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check) seen finish) :
    ∃ checkedLabels canonLabels reached mark,
      Steps profile ready (specDispatch ready base) start (.tau :: checkedLabels) finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (.tau :: canonLabels) reached ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older (PayloadPrefix.stringPlanResume cx steps checkNext)
        (PayloadPrefix.stringPlanResume cx steps canonNext)) finish reached ∧
      PayloadPrefix.visible checkedLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted ∧
      AllocatorMark profile ready base bindings older
        (LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check)
        (stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size incoming canon
          (PayloadPrefix.stringPlanResume cx steps canonNext)) checkedLabels canonLabels finish reached mark := by
  obtain ⟨_, _, paired⟩ := frame.string_realloc_pair (profile := profile) (ready := ready) (bindings := bindings)
    cx ptr oldSize alignment size steps checkNext canonNext checkAt canonAt
  obtain ⟨checkedLabels, canonLabels, reached, mark, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots,
    outside, checkTrail, canonTrail, movement⟩ :=
    replayMarked path embedder (fun _ _ edge => by cases edge with
      | existing previous => exact .inl ⟨_, previous⟩
      | current => exact .inr rfl) paired (frame.outside_installed (.pure .unit) (.pure .unit))
  have enterLeft := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    cx ptr oldSize alignment size steps checkNext start check checkAt
  have enterRight := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size steps canonNext incoming canon canonAt
  exact ⟨checkedLabels, canonLabels, reached, mark, .cons enterLeft checked, .cons enterRight canonical, final,
    checkSeen, canonSeen, growth, checkRoots, canonRoots, ⟨outside, checkTrail, canonTrail, movement⟩⟩

theorem collectionPrefix (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : start.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let area := layout destination.width element
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    ClosedCallbackPrefix bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first) seen finish →
    ∃ checkedLabels canonLabels reached mark,
      Steps profile ready (specDispatch ready base) start ([.tau, .tau, .tau] ++ checkedLabels) finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming ([.tau, .tau] ++ canonLabels) reached ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      PayloadPrefix.visible checkedLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted ∧
      AllocatorMark profile ready base bindings older
        (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first)
        (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
          incoming canon second) checkedLabels canonLabels finish reached mark ∧
      ComparedOccurrencePaths profile ready base bindings start incoming seen finish reached := by
  intro area first second path
  obtain ⟨_, _, paired⟩ := frame.collection_install_pair (profile := profile) (ready := ready) (bindings := bindings)
    destination inst type element entries output index checkNext canonNext width prepared checkAt canonAt
  have atCallback : HostFrame.Related.Paired (ReturnFrame.Extend older first second)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        incoming canon second) := paired
  obtain ⟨checkedLabels, canonLabels, reached, mark, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots,
    outside, checkTrail, canonTrail, movement⟩ :=
    replayMarked path embedder (fun _ _ edge => by cases edge with
      | existing previous => exact .inl ⟨_, previous⟩
      | current => exact .inr rfl) atCallback (frame.outside_installed (.pure .unit) (.pure .unit))
  have leftInstalls := fun place => (PayloadPrefix.collection_install_occurrences (profile := profile) (ready := ready)
    (dispatch := specDispatch ready base) destination inst type element entries output index start incoming check canon
    checkNext canonNext width prepared checkAt canonAt place).1
  have rightInstalls := fun place => (PayloadPrefix.collection_install_occurrences (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) destination inst type element entries output index
    start incoming check canon checkNext canonNext width prepared checkAt canonAt place).2
  have enterLeft := (prefix_survives (leftInstalls (.active 0 0))).1
  have enterRight := (prefix_survives (rightInstalls (.active 0 0))).1
  refine ⟨checkedLabels, canonLabels, reached, mark, append enterLeft checked, append enterRight canonical, final,
    checkSeen, canonSeen, growth, checkRoots, canonRoots, ⟨outside, checkTrail, canonTrail, movement⟩,
    [.tau, .tau, .tau] ++ checkedLabels, [.tau, .tau] ++ canonLabels, ?_, ?_, ?_, (HostFrame.Related.Paired.data final).1⟩
  · intro mark
    cases mark with
    | none =>
      obtain ⟨atCut, left, right⟩ := movement none
      exact ⟨atCut, (Trail.absent enterLeft).append left, (Trail.absent enterRight).append right⟩
    | some place =>
      obtain ⟨atCut, left, right⟩ := movement (some place.pushed)
      exact ⟨atCut, (leftInstalls place).toTrail.append left, (rightInstalls place).toTrail.append right⟩
  · exact checkSeen
  · exact canonSeen

theorem pop {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkTrace canonTrace : Trace grow sig}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {value : Ret (core3 grow)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (marked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkTrace canonTrace finish incoming (some (.active 0 0)))
    (paired : HostFrame.Related.Paired wider finish incoming)
    (returning : finish.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
    (installed : segmentAt (segmentStorage canonEntry) (.active 0 0) = some (.prog second)) :
    ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
      LinkedCallback.ChildFrameOver older finish incoming check canon ∧
      Step profile ready (specDispatch ready base) finish .tau { finish with ctl := check.control (first value) } ∧
      Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
        { incoming with ctl := canon.control (second value) } ∧
      RetainsBelowTop profile ready (specDispatch ready base) checkEntry (checkTrace ++ [.tau])
        { finish with ctl := check.control (first value) } ∧
      RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base))
        canonEntry (canonTrace ++ [.tau]) { incoming with ctl := canon.control (second value) } ∧
      CoupledOccurrencePaths profile ready base bindings checkEntry canonEntry (checkTrace ++ [.tau]) (canonTrace ++ [.tau])
        { finish with ctl := check.control (first value) } { incoming with ctl := canon.control (second value) } := by
  obtain ⟨place, eq, trail⟩ := marked.canonicalTrail.survives
  cases eq
  have atTop := (prefix_survives trail).2.trans installed
  obtain ⟨canon, frame, canonAt⟩ := LinkedCallback.marked_pop_frame paired marked.outside returning atTop
  obtain ⟨checkPlace, checkEq, checkTrail⟩ := marked.checkedTrail.survives
  cases checkEq
  refine ⟨canon, frame, .popProg returning, .popProg canonAt, ?_, ?_, ?_⟩
  · intro depth
    exact Prefix.append (by simpa only [Location.below, Nat.zero_add] using checkTrail.under (depth + 1))
      (Prefix.pop_return returning depth)
  · intro depth
    exact Prefix.append (by simpa only [Location.below, Nat.zero_add] using trail.under (depth + 1))
      (Prefix.pop_return canonAt depth)
  · intro mark
    obtain ⟨middle, lhs, rhs⟩ := marked.movement mark
    exact ⟨_, lhs.append (Trail.pop_prog middle returning), rhs.append (Trail.pop_prog middle canonAt)⟩

theorem popMovement {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkTrace canonTrace : Trace grow sig}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {value : Ret (core3 grow)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (marked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkTrace canonTrace finish incoming (some (.active 0 0)))
    (paired : HostFrame.Related.Paired wider finish incoming)
    (returning : finish.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
    (installed : segmentAt (segmentStorage canonEntry) (.active 0 0) = some (.prog second)) :
    ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
      LinkedCallback.ChildFrameOver older finish incoming check canon ∧
      incoming.ctl = { canon with frames := .prog second :: canon.frames }.control (.pure value) ∧
      CoupledOccurrencePaths profile ready base bindings checkEntry canonEntry (checkTrace ++ [.tau]) (canonTrace ++ [.tau])
        { finish with ctl := check.control (first value) } { incoming with ctl := canon.control (second value) } := by
  obtain ⟨place, same, tracked⟩ := marked.canonicalTrail.survives
  cases same
  have atTop := (prefix_survives tracked).2.trans installed
  obtain ⟨canon, frame, focused⟩ := LinkedCallback.marked_pop_frame paired marked.outside returning atTop
  refine ⟨canon, frame, focused, ?_⟩
  intro cursor
  obtain ⟨middle, leftTrail, rightTrail⟩ := marked.movement cursor
  exact ⟨_, leftTrail.append (Trail.pop_prog middle returning), rightTrail.append (Trail.pop_prog middle focused)⟩

private theorem stringInstallTracks (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cx : LiftLowerContext (core3 grow)) (pointer : Nat) (oldSize : Option Nat) (alignment : Alignment) (size : Nat)
    (rest : List StoreStep) (next : Nat → Session grow sig (Ret (core3 grow)))
    (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : state.ctl = cursor.control (runStoreSteps cx pointer
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: rest) >>= next))
    (depth : Nat) : Prefix profile ready dispatch state (.active 0 depth) [.tau]
      (stringAllocatorEntry dispatch cx pointer oldSize alignment size state cursor (PayloadPrefix.stringPlanResume cx rest next))
      (.active 0 (depth + 1)) :=
  .step (PayloadPrefix.string_realloc_install cx pointer oldSize alignment size rest next state cursor focused)
    (by rw [transitionEdit, focused, PayloadPrefix.string_realloc_focus]; rfl) (.done _ _)

private theorem stringInstallTrail (dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (cx : LiftLowerContext (core3 grow)) (pointer : Nat) (oldSize : Option Nat) (alignment : Alignment) (size : Nat)
    (rest : List StoreStep) (next : Nat → Session grow sig (Ret (core3 grow)))
    (state : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig))
    (focused : state.ctl = cursor.control (runStoreSteps cx pointer
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: rest) >>= next))
    (mark : Option Location) : Trail profile ready dispatch state mark [.tau]
      (stringAllocatorEntry dispatch cx pointer oldSize alignment size state cursor (PayloadPrefix.stringPlanResume cx rest next))
      (mark.map Location.pushed) := by
  refine .step (PayloadPrefix.string_realloc_install cx pointer oldSize alignment size rest next state cursor focused) ?_
  rw [transitionEdit, focused, PayloadPrefix.string_realloc_focus]
  rcases mark with _ | ⟨place⟩
  · exact .done _ _
  · cases place with
    | active activation segment => cases activation <;> exact .done _ _
    | saved => exact .done _ _

theorem stringReplay (cx : LiftLowerContext (core3 grow)) (pointer : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (checkAt : left.ctl = check.control (runStoreSteps cx pointer steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx pointer steps >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {ends : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    (finish : ∀ pointer lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext pointer) →
      rhs.ctl = canon.control (canonNext pointer) → ends pointer lhs rhs check canon) :
    LiveStringReplay profile ready base bindings older cx checkNext canonNext ends steps.length left right check canon := by
  induction measured : steps.length using Nat.strong_induction_on generalizing pointer steps left right check canon with
  | ind length ih =>
    have cut := PayloadPrefix.string_front_occurrences (profile := profile) (ready := ready)
      (dispatch := specDispatch ready base) (reference := specDispatch ready (LiveDispatch.host bindings base))
      cx pointer steps left right check canon checkNext canonNext frame.store checkAt canonAt
    rw [measured] at cut
    obtain ⟨store, result, labels, observed, checked, canonical, tracked, trails⟩ := cut
    rw [LiveStringReplay]
    refine ⟨store, result, labels, observed, checked, canonical, (fun mark => ⟨_, (trails mark).1, (trails mark).2⟩), ?_⟩
    intro front success
    subst result
    refine ⟨fun depth => (tracked front rfl depth).1, fun depth => (tracked front rfl depth).2, ?_⟩
    cases front with
    | done value =>
      exact finish value _ _ check canon
        ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        (growth.trans checked.grows) rfl rfl
    | call ptr oldSize alignment size rest shorter =>
      dsimp only
      intro seen reached path
      let action : StoreStep := oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)
      let lhs := { left with store, ctl := check.control (runStoreSteps cx ptr (action :: rest) >>= checkNext) }
      let rhs := { right with store, ctl := canon.control (runStoreSteps cx ptr (action :: rest) >>= canonNext) }
      have middle : LinkedCallback.ChildFrameOver older lhs rhs check canon :=
        ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
      obtain ⟨checkLabels, canonLabels, reference, mark, leftRun, rightRun, paired, checkSeen, canonSeen,
        callGrowth, checkedRoots, canonRoots, marked⟩ := stringReallocPrefix (profile := profile) (ready := ready)
        cx ptr oldSize alignment size rest checkNext canonNext middle rfl rfl embedder path
      let checkEntry := LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size rest checkNext lhs check
      let canonEntry := stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base))
        cx ptr oldSize alignment size rhs canon (PayloadPrefix.stringPlanResume cx rest canonNext)
      have prependInstall {endLeft endRight : Config (core3 grow) (HostState sig)} {leftTail rightTail : Trace grow sig}
          (tail : CoupledOccurrencePaths profile ready base bindings checkEntry canonEntry leftTail rightTail endLeft endRight) :
          CoupledOccurrencePaths profile ready base bindings lhs rhs (.tau :: leftTail) (.tau :: rightTail) endLeft endRight := by
        intro mark
        have checkInstall : Trail profile ready (specDispatch ready base) lhs mark [.tau] checkEntry (mark.map Location.pushed) :=
          stringInstallTrail _ cx ptr oldSize alignment size rest checkNext lhs check rfl mark
        have canonInstall : Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) rhs mark [.tau]
            canonEntry (mark.map Location.pushed) := stringInstallTrail _ cx ptr oldSize alignment size rest canonNext rhs canon rfl mark
        obtain ⟨reached, checkTail, canonTail⟩ := tail (mark.map Location.pushed)
        exact ⟨reached, checkInstall.append checkTail, canonInstall.append canonTail⟩
      refine ⟨checkLabels, canonLabels, reference, mark, leftRun, rightRun, checkSeen, canonSeen, paired,
        callGrowth, checkedRoots, canonRoots, marked, prependInstall marked.movement, ?_⟩
      intro value cursor atMark returning
      cases atMark
      obtain ⟨peer, residual, _, _, leftPop, rightPop, movement⟩ := pop marked paired returning rfl
      refine ⟨peer, ?_, ?_, ?_, ?_⟩
      · exact fun depth => (stringInstallTracks _ cx ptr oldSize alignment size rest checkNext lhs check rfl depth).append
          (leftPop depth)
      · exact fun depth => (stringInstallTracks _ cx ptr oldSize alignment size rest canonNext rhs canon rfl depth).append
          (rightPop depth)
      · exact prependInstall movement
      · exact ih rest.length shorter value rest
          (show LinkedCallback.ChildFrameOver older
            { reached with ctl := cursor.control (runStoreSteps cx value rest >>= checkNext) }
            { reference with ctl := peer.control (runStoreSteps cx value rest >>= canonNext) } cursor peer from
            ⟨residual.store, residual.pending, residual.results, residual.cancels, residual.blocked, residual.thread,
              residual.frames, residual.rest⟩)
          ((growth.trans checked.grows).trans callGrowth) rfl rfl rfl

theorem stringReplayMap {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {first second : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    (next : ∀ pointer lhs rhs check canon, first pointer lhs rhs check canon → second pointer lhs rhs check canon)
    {length : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (run : LiveStringReplay profile ready base bindings older cx checkNext canonNext first length left right check canon) :
    LiveStringReplay profile ready base bindings older cx checkNext canonNext second length left right check canon := by
  induction length using Nat.strong_induction_on generalizing left right check canon with
  | ind length ih =>
    rw [LiveStringReplay] at run ⊢
    obtain ⟨store, result, labels, observed, checked, canonical, localTrails, nextCut⟩ := run
    refine ⟨store, result, labels, observed, checked, canonical, localTrails, ?_⟩
    intro front success
    obtain ⟨tracksLeft, tracksRight, matched⟩ := nextCut front success
    refine ⟨tracksLeft, tracksRight, ?_⟩
    cases front with
    | done pointer => exact next pointer _ _ _ _ matched
    | call ptr oldSize alignment size rest shorter =>
      intro seen reached path
      obtain ⟨checkLabels, canonLabels, reference, mark, lhs, rhs, checkSeen, canonSeen, paired,
        growth, checkRoots, canonRoots, marked, trails, returning⟩ := matched path
      refine ⟨checkLabels, canonLabels, reference, mark, lhs, rhs, checkSeen, canonSeen, paired,
        growth, checkRoots, canonRoots, marked, trails, ?_⟩
      intro value cursor atMark focus
      obtain ⟨peer, checked, canonical, movement, tail⟩ := returning value cursor atMark focus
      exact ⟨peer, checked, canonical, movement, ih rest.length shorter tail⟩

theorem appendComparedSlots {leftStart rightStart left right lhs rhs : Config (core3 grow) (HostState sig)}
    {before after : Trace grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart before left right offset)
    (trailing : ComparedSlots profile ready base bindings left right after lhs rhs) :
    ComparedSlots profile ready base bindings leftStart rightStart (before ++ after) lhs rhs offset := by
  obtain ⟨checkLabels, canonLabels, checkTracks, canonTracks, checkSeen, canonSeen⟩ := leading
  obtain ⟨leftLabels, rightLabels, leftTracks, rightTracks, leftSeen, rightSeen⟩ := trailing
  exact ⟨checkLabels ++ leftLabels, canonLabels ++ rightLabels,
    fun depth => (checkTracks depth).append (leftTracks depth), fun depth => (canonTracks depth).append (rightTracks depth),
    (List.filter_append ..).trans (congrArg₂ List.append checkSeen leftSeen),
    (List.filter_append ..).trans (congrArg₂ List.append canonSeen rightSeen)⟩

theorem appendComparedOccurrences {leftStart rightStart left right lhs rhs : Config (core3 grow) (HostState sig)}
    {before after : Trace grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings leftStart rightStart before left right)
    (trailing : ComparedOccurrencePaths profile ready base bindings left right after lhs rhs) :
    ComparedOccurrencePaths profile ready base bindings leftStart rightStart (before ++ after) lhs rhs := by
  obtain ⟨checkLabels, canonLabels, beforePaths, checkSeen, canonSeen, _⟩ := leading
  obtain ⟨leftLabels, rightLabels, afterPaths, leftSeen, rightSeen, shared⟩ := trailing
  refine ⟨checkLabels ++ leftLabels, canonLabels ++ rightLabels, ?_,
    (List.filter_append ..).trans (congrArg₂ List.append checkSeen leftSeen),
    (List.filter_append ..).trans (congrArg₂ List.append canonSeen rightSeen), shared⟩
  intro mark
  obtain ⟨middle, checkTrail, canonTrail⟩ := beforePaths mark
  obtain ⟨reached, leftTrail, rightTrail⟩ := afterPaths middle
  exact ⟨reached, checkTrail.append leftTrail, canonTrail.append rightTrail⟩

theorem stringOccurrences {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {leftStart rightStart left right : Config (core3 grow) (HostState sig)}
    {ends : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    {length : Nat} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leading : ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left right)
    (run : LiveStringReplay profile ready base bindings older cx checkNext canonNext ends length left right check canon) :
    LiveStringOccurrences profile ready base bindings older cx checkNext canonNext leftStart rightStart ends length left right check canon seen := by
  induction length using Nat.strong_induction_on generalizing left right check canon seen with
  | ind length ih =>
    rw [LiveStringReplay] at run
    rw [LiveStringOccurrences]
    obtain ⟨store, result, labels, observed, _, _, localTrails, nextCut⟩ := run
    have reached := appendComparedOccurrences leading ⟨labels, labels, localTrails, rfl, rfl, by cases result <;> rfl⟩
    refine ⟨store, result, labels, observed, reached, ?_⟩
    cases result with
    | error => exact ⟨rfl, rfl⟩
    | ok front =>
      obtain ⟨_, _, matched⟩ := nextCut front rfl
      have silent : PayloadPrefix.visible labels = [] := visibleLeaf observed
      rw [silent, List.append_nil] at reached
      cases front with
      | done => exact matched
      | call ptr oldSize alignment size rest shorter =>
        intro observed reachedCall path
        obtain ⟨checkLabels, canonLabels, reference, mark, _, _, checkSeen, canonSeen, paired,
          _, _, _, marked, movement, returning⟩ := matched path
        have sameStore := (HostFrame.Related.Paired.data paired).1
        refine ⟨checkLabels, canonLabels, reference, mark, marked, paired,
          appendComparedOccurrences reached ⟨_, _, movement, checkSeen, canonSeen, sameStore⟩, ?_⟩
        intro value cursor atMark focus
        obtain ⟨peer, _, _, returned, residual⟩ := returning value cursor atMark focus
        have silentPop (raw : Trace grow sig) (observedAs : PayloadPrefix.visible raw = observed) :
            PayloadPrefix.visible (.tau :: raw ++ [.tau]) = observed := by
          change PayloadPrefix.visible (raw ++ [.tau]) = observed
          rw [show PayloadPrefix.visible (raw ++ [.tau]) = PayloadPrefix.visible raw ++
            PayloadPrefix.visible ([.tau] : Trace grow sig) from List.filter_append .., observedAs]
          simp [PayloadPrefix.visible]
        have afterPop := appendComparedOccurrences reached
          ⟨_, _, returned, silentPop _ checkSeen, silentPop _ canonSeen, sameStore⟩
        exact ⟨peer, afterPop, ih rest.length shorter afterPop residual⟩

theorem appendComparedPaths {leftStart rightStart left right lhs rhs : Config (core3 grow) (HostState sig)}
    {before after : Trace grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart before left right offset)
    (trailing : ComparedPaths profile ready base bindings left right after lhs rhs) :
    ComparedPaths profile ready base bindings leftStart rightStart (before ++ after) lhs rhs := by
  obtain ⟨checkLabels, canonLabels, checkTracks, canonTracks, checkSeen, canonSeen⟩ := leading
  obtain ⟨leftLabels, rightLabels, leftRun, rightRun, leftSeen, rightSeen, same⟩ := trailing
  exact ⟨checkLabels ++ leftLabels, canonLabels ++ rightLabels,
    append (prefix_survives (checkTracks 0)).1 leftRun, append (prefix_survives (canonTracks 0)).1 rightRun,
    (List.filter_append ..).trans (congrArg₂ List.append checkSeen leftSeen),
    (List.filter_append ..).trans (congrArg₂ List.append canonSeen rightSeen), same⟩

theorem appendAllocatorPaths {leftStart rightStart left right lhs rhs : Config (core3 grow) (HostState sig)}
    {before after : Trace grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart before left right offset)
    (trailing : ComparedAllocatorPaths profile ready base bindings left right after lhs rhs) :
    ComparedAllocatorPaths profile ready base bindings leftStart rightStart (before ++ after) lhs rhs offset := by
  obtain ⟨checkLabels, canonLabels, checkTracks, canonTracks, checkSeen, canonSeen⟩ := leading
  obtain ⟨leftLabels, rightLabels, movement, leftSeen, rightSeen, same⟩ := trailing
  refine ⟨checkLabels ++ leftLabels, canonLabels ++ rightLabels, ?_,
    (List.filter_append ..).trans (congrArg₂ List.append checkSeen leftSeen),
    (List.filter_append ..).trans (congrArg₂ List.append canonSeen rightSeen), same⟩
  intro depth
  obtain ⟨reached, leftTrail, rightTrail⟩ := movement depth
  exact ⟨reached, (checkTracks depth).toTrail.append leftTrail, (canonTracks depth).toTrail.append rightTrail⟩

theorem allocatorPaths {left right checkEntry canonEntry : Config (core3 grow) (HostState sig)}
    {checkFront canonFront checkLabels canonLabels observed : Trace grow sig} {mark : Option Location}
    (installedCheck : ∀ depth, Prefix profile ready (specDispatch ready base) left (.active 0 depth) checkFront
      checkEntry (.active 0 (depth + 1)))
    (installedCanon : ∀ depth, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right
      (.active 0 depth) canonFront canonEntry (.active 0 (depth + 1)))
    (tracked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkLabels canonLabels finish incoming mark)
    (checkSeen : PayloadPrefix.visible (checkFront ++ checkLabels) = observed)
    (canonSeen : PayloadPrefix.visible (canonFront ++ canonLabels) = observed) (same : finish.store = incoming.store) :
    ComparedAllocatorPaths profile ready base bindings left right observed finish incoming := by
  refine ⟨_, _, ?_, checkSeen, canonSeen, same⟩
  intro depth
  obtain ⟨reached, leftTrail, rightTrail⟩ := tracked.movement (some (.active 0 (depth + 1)))
  exact ⟨reached, (installedCheck depth).toTrail.append leftTrail, (installedCanon depth).toTrail.append rightTrail⟩

theorem allocatorSteps {left right : Config (core3 grow) (HostState sig)} {offset : Nat}
    (paths : ComparedAllocatorPaths profile ready base bindings left right seen finish incoming offset) :
    ComparedPaths profile ready base bindings left right seen finish incoming := by
  have run {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {left right front back labels}
      (trail : Trail profile ready dispatch left front labels right back) : Steps profile ready dispatch left labels right := by
    induction trail with
    | done => exact .refl _
    | step step _ ih => exact .cons step ih
  obtain ⟨checkLabels, canonLabels, movement, lhs, rhs, same⟩ := paths
  obtain ⟨_, checked, canonical⟩ := movement 0
  exact ⟨checkLabels, canonLabels, run checked, run canonical, lhs, rhs, same⟩

theorem replayBetweenPathsFrom {mode : LinkedCallback.MemorySequence.Track} {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {entries : List Field} {index address offset : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {sink : RefusalSink grow sig}
    (lift : LiftsFieldPaths profile ready base bindings start incoming offset child paths sink)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (same : left.store = right.store)
    (run : LinkedCallback.MemorySequence.ReplayBetween profile ready (specDispatch ready (LiveDispatch.host bindings base))
      mode destination inst child checkNext canonNext finish entries index address left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    replayBetweenPaths profile ready base bindings mode destination inst paths checkNext canonNext visit
      entries index address seen left right check canon := by
  induction entries generalizing index address seen left right check canon with
  | nil => exact next seen left right check canon leading same run
  | cons item rest ih =>
    rw [LinkedCallback.MemorySequence.ReplayBetween] at run
    rw [replayBetweenPaths]
    obtain ⟨read, body⟩ := run
    have quiet : PayloadPrefix.visible (mode.readLabels (grow := grow) (sig := sig)) = [] := by cases mode <;> rfl
    have reached := appendComparedSlots (after := []) leading ⟨[], _, (fun _ => .done _ _), read, rfl, quiet⟩
    rw [List.append_nil] at reached
    exact ⟨read, lift _ _ _ _ _ _ _ _ _ _ _ _ body reached same admitted
      (fun _ _ _ _ _ tracks shared tail => ih tracks shared tail)⟩

theorem liveElementsPathsFrom {destination : RecordDestination} {inst : InstId} {stride : Nat}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {entries : List Field} {index address offset : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {sink : RefusalSink grow sig}
    (lift : LiftsFieldPaths profile ready base bindings start incoming offset child paths sink)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (same : left.store = right.store)
    (run : liveElements destination inst stride child checkNext canonNext finish entries index address left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveElementsPaths destination inst stride paths checkNext canonNext visit entries index address seen left right check canon := by
  induction entries generalizing index address seen left right check canon with
  | nil => exact next seen left right check canon leading same run
  | cons item rest ih =>
    rw [liveElements] at run
    rw [liveElementsPaths]
    exact lift _ _ _ _ _ _ _ _ _ _ _ _ run leading same admitted
      (fun _ _ _ _ _ tracks shared tail => ih tracks shared tail)

theorem stringPaths {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {leftStart rightStart : Config (core3 grow) (HostState sig)}
    {first : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    {second : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Trace grow sig → Prop}
    {offset : Nat} (next : ∀ ptr lhs rhs check canon seen, first ptr lhs rhs check canon →
      ComparedSlots profile ready base bindings leftStart rightStart seen lhs rhs offset → second ptr lhs rhs check canon seen)
    {length : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {seen : Trace grow sig}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart seen left right offset)
    (run : LiveStringReplay profile ready base bindings older cx checkNext canonNext first length left right check canon) :
    LiveStringPaths profile ready base bindings older cx checkNext canonNext leftStart rightStart second length left right check canon seen offset := by
  induction length using Nat.strong_induction_on generalizing left right check canon seen with
  | ind length ih =>
    rw [LiveStringReplay] at run
    rw [LiveStringPaths]
    obtain ⟨store, result, labels, observed, checked, canonical, _, nextCut⟩ := run
    refine ⟨store, result, labels, observed, checked.steps, canonical.steps, ?_⟩
    cases result with
    | error reason =>
      have atTrap : PayloadPrefix.visible labels = [.trap reason] := visibleLeaf observed
      exact ⟨rfl, rfl, appendComparedPaths leading ⟨labels, labels, checked.steps, canonical.steps, atTrap, atTrap, rfl⟩⟩
    | ok front =>
      obtain ⟨checkLocal, canonLocal, matched⟩ := nextCut front rfl
      have noLabels : PayloadPrefix.visible labels = [] := visibleLeaf observed
      have reached := appendComparedSlots leading ⟨labels, labels, checkLocal, canonLocal, noLabels, noLabels⟩
      rw [List.append_nil] at reached
      cases front with
      | done pointer => exact ⟨reached, next pointer _ _ _ _ seen matched reached⟩
      | call ptr oldSize alignment size rest shorter =>
        intro observed reachedCall path
        obtain ⟨checkLabels, canonLabels, reference, mark, _, _, checkSeen, canonSeen, paired,
          _, _, _, marked, _, returning⟩ := matched path
        have sameStore := HostFrame.Related.Paired.data paired |>.1
        have live := allocatorPaths
          (stringInstallTracks _ cx ptr oldSize alignment size rest checkNext _ check rfl)
          (stringInstallTracks _ cx ptr oldSize alignment size rest canonNext _ canon rfl)
          marked checkSeen canonSeen sameStore
        refine ⟨checkLabels, canonLabels, reference, mark, marked, paired, appendAllocatorPaths reached live, ?_⟩
        intro value cursor atMark focus
        obtain ⟨peer, checked, canonical, _, tail⟩ := returning value cursor atMark focus
        have checkPopped : PayloadPrefix.visible (.tau :: checkLabels ++ [.tau]) = observed := by
          change PayloadPrefix.visible (checkLabels ++ [.tau]) = observed
          rw [show PayloadPrefix.visible (checkLabels ++ [.tau]) = PayloadPrefix.visible checkLabels ++
            PayloadPrefix.visible ([.tau] : Trace grow sig) from List.filter_append .., checkSeen]; simp [PayloadPrefix.visible]
        have canonPopped : PayloadPrefix.visible (.tau :: canonLabels ++ [.tau]) = observed := by
          change PayloadPrefix.visible (canonLabels ++ [.tau]) = observed
          rw [show PayloadPrefix.visible (canonLabels ++ [.tau]) = PayloadPrefix.visible canonLabels ++
            PayloadPrefix.visible ([.tau] : Trace grow sig) from List.filter_append .., canonSeen]; simp [PayloadPrefix.visible]
        exact ⟨peer, ih rest.length shorter (appendComparedSlots reached ⟨_, _, checked, canonical, checkPopped, canonPopped⟩) tail⟩

theorem stringValuePaths {destination : RecordDestination} {inst : InstId} {key : LinkedCallback.StringField}
    {output : Stored.Lower.Output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {first : Nat → LinkedCallback.MemorySequence.Finish grow sig}
    {second : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : StringValueThen profile ready base bindings older destination inst key output left right check canon checkNext canonNext first)
    (next : ∀ ptr lhs rhs check canon observed, first ptr lhs rhs check canon →
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → second ptr observed lhs rhs check canon) :
    StringValuePaths profile ready base bindings older destination inst key output start incoming left right check canon
      checkNext canonNext second seen offset := by
  obtain ⟨checkLabels, canonLabels, checkSeen, canonSeen, checkEntry, canonEntry, _, body⟩ := run
  have reached := appendComparedSlots leading ⟨checkLabels, canonLabels, checkEntry, canonEntry, checkSeen, canonSeen⟩
  rw [List.append_nil] at reached
  exact stringPaths next reached body

theorem localFieldPaths {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : LiveLocalFieldThen profile ready base bindings checkNext canonNext finish left right check canon)
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalPathsThen profile ready base bindings start incoming seen offset visit := by
  obtain ⟨store, result, lhsLabels, rhsLabels, lhs, rhs, same, cut⟩ := run
  cases result with
  | error reason =>
    obtain ⟨before, trapped⟩ := cut
    exact .inl ⟨reason, before, _, _, appendComparedPaths leading
      ⟨lhsLabels, rhsLabels, lhs, rhs, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok value =>
    cases value
    obtain ⟨lhsTrack, rhsTrack, done⟩ := cut
    have reached := appendComparedSlots leading ⟨lhsLabels, rhsLabels, lhsTrack, rhsTrack, rfl, same.symm⟩
    exact .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, reached, rfl, next _ _ _ _ _ reached rfl done⟩

theorem compiledStringPaths {destination : RecordDestination} {inst : InstId}
    {item : Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : liveCollectionField profile ready base bindings older destination inst (.prim .string) item index address
      left right check canon checkNext canonNext finish)
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    ∃ str : LinkedCallback.StringField, item = str.field ∧
      StringKeyPaths profile ready base bindings older destination inst str address start incoming left right check canon
        checkNext canonNext (fun _ observed _ _ _ _ =>
          LocalPathsThen profile ready base bindings start incoming observed offset visit) seen offset := by
  obtain ⟨str, field, body⟩ := run
  exact ⟨str, field, stringValuePaths leading body
    (fun _ _ _ _ _ _ descriptors path => localFieldPaths path descriptors next)⟩

theorem handleValuePaths {item : Field} {index offset : Nat} {output : Stored.Lower.Output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {finish : output.Result → LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (same : left.store = right.store)
    (run : LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index output left right check canon checkNext canonNext finish)
    {sink : RefusalSink grow sig}
    (covers : sink.Covers profile ready base bindings start incoming offset)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    HandlePathsThen profile ready base bindings start incoming seen offset item index checkNext visit left right check sink := by
  unfold LinkedCallback.HandleFieldThenBetween at run
  cases decision : liveLeafPlan left.store left.host.writer index item with
  | error issue =>
    rw [decision] at run
    obtain ⟨labels, tau, retained⟩ := run
    have silent := invisible (List.all_eq_true.mpr (fun label member => by rw [tau label member]))
    have reached := appendComparedSlots leading ⟨labels, [], retained, fun depth => .done _ _, silent, rfl⟩
    rw [List.append_nil] at reached
    exact .inl ⟨issue, decision, reached, same, covers _ admitted issue seen _ _ check rfl same reached⟩
  | ok plan =>
    rw [decision] at run
    obtain ⟨store, result, guard, lhsLabels, rhsLabels, tau, lhsKind, rhsKind, lhsRun, rhsRun, continued⟩ := run
    have silent : PayloadPrefix.visible guard = [] :=
      invisible (List.all_eq_true.mpr (fun label member => by rw [tau label member]))
    have lhsSeen := (List.filter_append ..).trans (congrArg₂ List.append silent (visibleLeaf lhsKind))
    cases result with
    | error reason =>
      exact .inr (.inl ⟨reason, [], _, _, appendComparedPaths leading
        ⟨_, _, lhsRun, rhsRun, lhsSeen, visibleLeaf rhsKind, rfl⟩, rfl, rfl⟩)
    | ok result =>
      obtain ⟨lhsTrack, rhsTrack, done⟩ := continued result rfl
      have reached := appendComparedSlots leading ⟨_, _, lhsTrack, rhsTrack, lhsSeen, visibleLeaf rhsKind⟩
      exact .inr (.inr ⟨[], _, _, check, canon, reached, rfl, next result _ _ _ _ _ reached rfl done⟩)

theorem handleFieldPaths {item : Field} {index address offset : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (same : left.store = right.store)
    (run : LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index (.memory address) left right check canon
      checkNext canonNext (fun () => finish))
    {sink : RefusalSink grow sig} (covers : sink.Covers profile ready base bindings start incoming offset)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    HandlePathsThen profile ready base bindings start incoming seen offset item index checkNext visit left right check sink :=
  handleValuePaths leading same run covers admitted (fun () => next)

theorem leafFieldLift {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf} {offset : Nat}
    {sink : RefusalSink grow sig} (covers : sink.Covers profile ready base bindings start incoming offset)
    (leaf : TrailLeafType type) :
    LiftsFieldPaths profile ready base bindings start incoming offset
      (liveCollectionField profile ready base bindings older destination inst type)
      (liveLeafPaths profile ready base bindings older destination inst start incoming offset sink type) sink := by
  rcases leaf with nominal | data | rfl
  · cases nominal <;> intro _ _ _ _ _ _ _ _ _ _ _ _ run leading same admitted next <;>
      exact handleFieldPaths leading same run covers admitted next
  · cases data with
    | @primitive primitive nons =>
      cases primitive <;> first
        | exact (nons rfl).elim
        | intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ _ next; exact localFieldPaths leading run next
    | enum | flags =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ _ next
      exact localFieldPaths leading run next
  · intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ _ next
    exact compiledStringPaths leading run next

theorem aggregateChildLift {comparisons : List (Stored.TypeOf × LinkedCallback.MemorySequence.FieldComparison grow sig)}
    {paths : Stored.TypeOf → TrailFieldComparison grow sig} {offset : Nat} {sink : RefusalSink grow sig}
    (lift : ∀ type raw, (type, raw) ∈ comparisons → LiftsFieldPaths profile ready base bindings start incoming offset raw (paths type) sink) :
    LiftsFieldPaths profile ready base bindings start incoming offset (aggregateChild comparisons) (selectFieldPaths paths) sink := by
  intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
  obtain ⟨raw, member, body⟩ := run
  exact lift item.type raw member item index address left right check canon checkNext canonNext finish visit before body leading same admitted next

theorem aggregatePathsFrom {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {items : List Field} {index address offset : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {sink : RefusalSink grow sig}
    (lift : LiftsFieldPaths profile ready base bindings start incoming offset child paths sink)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (same : left.store = right.store)
    (run : LiveAggregateThen profile ready base bindings destination inst child items index address checkNext canonNext finish
      left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveAggregatePaths profile ready base bindings destination inst paths items index address checkNext canonNext visit
      seen left right check canon := by
  obtain ⟨read, body⟩ := run
  have reached := appendComparedSlots (after := []) leading ⟨[.tau], [], read, (fun _ => .done _ _), rfl, rfl⟩
  rw [List.append_nil] at reached
  exact ⟨read, replayBetweenPathsFrom lift reached same body (sink.nested _ admitted index) next⟩

theorem recordTable (destination : RecordDestination) (inst : InstId) (fields : List (String × Stored.TypeOf)) :
    liveRecordFields profile ready base bindings older destination inst fields =
      liveTupleFields profile ready base bindings older destination inst (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    cases field
    simp only [liveRecordFields, List.map_cons, liveTupleFields, ih]

theorem tupleFieldLift {destination : RecordDestination} {inst : InstId} {types : List Stored.TypeOf} {offset : Nat}
    (leaves : ∀ type ∈ types, TrailLeafType type) :
    LiftsFieldPaths profile ready base bindings start incoming offset
      (aggregateChild (liveTupleFields profile ready base bindings older destination inst types))
      (selectFieldPaths (liveLeafPaths profile ready base bindings older destination inst start incoming offset)) := by
  apply aggregateChildLift
  intro type raw member
  induction types with
  | nil => cases member
  | cons schema rest ih =>
    rw [liveTupleFields] at member
    rcases List.mem_cons.mp member with equal | later
    · cases equal
      exact leafFieldLift (fun _ _ _ _ _ _ _ _ _ _ => True.intro) (leaves _ (List.mem_cons_self ..))
    · exact ih (fun item present => leaves item (List.mem_cons_of_mem _ present)) later

theorem leafAggregateLift {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf} {offset : Nat}
    (leaves : TrailLeafAggregate type) :
    LiftsFieldPaths profile ready base bindings start incoming offset
      (liveCollectionField profile ready base bindings older destination inst type)
      (aggregateFieldPaths profile ready base bindings destination inst type
        (liveLeafPaths profile ready base bindings older destination inst start incoming offset)) := by
  cases leaves with
  | @record fields declared =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨items, aligned, body⟩ := run
    rw [recordTable destination inst] at body
    have types : ∀ field ∈ fields.map Prod.snd, TrailLeafType field := by
      intro type member
      obtain ⟨field, inFields, rfl⟩ := List.mem_map.mp member
      exact declared field inFields
    exact ⟨items, aligned, aggregatePathsFrom (tupleFieldLift types) leading same body admitted next⟩
  | tuple declared =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨items, aligned, body⟩ := run
    exact ⟨items, aligned, aggregatePathsFrom (tupleFieldLift declared) leading same body admitted next⟩

theorem sumPathsFrom {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {arms : List (Option Stored.TypeOf)} {selected : Option Field} {index address offset : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {sink : RefusalSink grow sig}
    (lift : selected.isSome = true → LiftsFieldPaths profile ready base bindings start incoming offset child paths sink)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : LiveSumThen profile ready base bindings destination inst child arms selected index address
      checkNext canonNext finish left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalPathsThen profile ready base bindings start incoming seen offset
      (match selected with
      | none => visit
      | some item => paths item 0 (PayloadPrefix.sumPayloadAddress destination.width arms address)
          (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext visit) := by
  obtain ⟨store, result, lhsLabels, rhsLabels, lhsRun, rhsRun, same, tail⟩ := run
  cases result with
  | error reason =>
    obtain ⟨prefixLabels, trapped⟩ := tail
    exact .inl ⟨reason, prefixLabels, _, _, appendComparedPaths leading
      ⟨lhsLabels, rhsLabels, lhsRun, rhsRun, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok result =>
    cases result
    obtain ⟨lhsTrack, rhsTrack, done⟩ := tail
    have reached := appendComparedSlots leading ⟨lhsLabels, rhsLabels, lhsTrack, rhsTrack, rfl, same.symm⟩
    refine .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, reached, rfl, ?_⟩
    cases selected with
    | none => exact next _ _ _ _ _ reached rfl done
    | some item =>
      exact lift rfl item 0 _ _ _ check canon _ canonNext finish visit _ done reached rfl
        (sink.nested _ admitted index) next

theorem stringMapEntryPaths {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {output : Stored.Lower.Output} {field value : Field} {index slot offset : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {compare : LinkedCallback.MemorySequence.FieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : Nat → TrailFinish grow sig}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : LiveStringMapEntryThen profile ready base bindings older destination inst element output
      field value index slot compare checkNext canonNext finish left right check canon)
    (next : ∀ ptr observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      compare value 1 ptr lhs rhs cursor peer (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish →
      visit ptr observed lhs rhs cursor peer) :
    LiveStringMapEntryPaths profile ready base bindings older destination inst element output start incoming seen offset
      field value index slot checkNext canonNext visit left right check canon := by
  obtain ⟨key, keyField, body⟩ := run
  refine ⟨key, keyField, stringValuePaths leading body ?_⟩
  intro pointer lhs rhs cursor peer observed descriptors path
  obtain ⟨store, result, labels, kind, lhsRun, rhsRun, tail⟩ := descriptors
  cases result with
  | error reason =>
    have trace : PayloadPrefix.visible labels = [.trap reason] := visibleLeaf kind
    exact .inl ⟨reason, [], _, _, appendComparedPaths path ⟨labels, labels, lhsRun.steps, rhsRun.steps, trace, trace, rfl⟩, rfl, rfl⟩
  | ok result =>
    cases result
    obtain ⟨lhsTrack, rhsTrack, widthRead, widthSilent, widthTrack, valueRun⟩ := tail
    have silent : PayloadPrefix.visible labels = [] := visibleLeaf kind
    have reached := appendComparedSlots path ⟨labels, labels ++ widthRead, lhsTrack,
      fun depth => (rhsTrack depth).append (widthTrack depth), silent,
      (List.filter_append ..).trans (congrArg₂ List.append silent widthSilent)⟩
    exact .inr ⟨[], _, _, cursor, peer, reached, rfl, next _ _ _ _ _ _ reached rfl valueRun⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
