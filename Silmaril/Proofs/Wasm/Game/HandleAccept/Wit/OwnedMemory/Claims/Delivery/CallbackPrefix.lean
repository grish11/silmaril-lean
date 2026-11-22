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

theorem transportPaths {left right lhs rhs : Config (core3 grow) (HostState sig)}
    {checked canonical : Trace grow sig} {introduced : List (Option Location)}
    (transport : OccurrenceTransport profile ready base bindings left right checked canonical lhs rhs introduced) :
    CoupledOccurrencePaths profile ready base bindings left right checked canonical lhs rhs := by
  obtain ⟨move, trails, _⟩ := transport
  exact fun cursor => ⟨move cursor, trails cursor⟩

theorem transportAppend {leftStart rightStart left right lhs rhs : Config (core3 grow) (HostState sig)}
    {checked canonical moreChecked moreCanonical : Trace grow sig} {introduced further : List (Option Location)}
    (first : OccurrenceTransport profile ready base bindings leftStart rightStart checked canonical left right introduced)
    (second : OccurrenceTransport profile ready base bindings left right moreChecked moreCanonical lhs rhs further) :
    ∃ moved, OccurrenceTransport profile ready base bindings leftStart rightStart (checked ++ moreChecked)
      (canonical ++ moreCanonical) lhs rhs (further ++ introduced.map moved) ∧
      ∀ cursor, Trail profile ready (specDispatch ready base) left cursor moreChecked lhs (moved cursor) ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) right cursor moreCanonical rhs (moved cursor) := by
  obtain ⟨move, paths, kept⟩ := first
  obtain ⟨next, tails, framed⟩ := second
  refine ⟨next, ⟨next ∘ move, ?_, ?_⟩, tails⟩
  · intro cursor
    obtain ⟨left, right⟩ := paths cursor
    obtain ⟨lhs, rhs⟩ := tails (move cursor)
    exact ⟨left.append lhs, right.append rhs⟩
  · intro older marks invariant
    simpa only [List.map_append, List.map_map, List.append_assoc] using framed older _ (kept older _ invariant)

theorem comparedTransportPaths {leftStart rightStart left right : Config (core3 grow) (HostState sig)}
    (run : ComparedOccurrenceTransport profile ready base bindings leftStart rightStart seen left right) :
    ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left right := by
  obtain ⟨checked, canonical, movement, checkSeen, canonSeen, store⟩ := run
  exact ⟨checked, canonical, transportPaths movement, checkSeen, canonSeen, store⟩

theorem appendComparedTransport {leftStart rightStart left right lhs rhs : Config (core3 grow) (HostState sig)}
    {more : Trace grow sig}
    (first : ComparedOccurrenceTransport profile ready base bindings leftStart rightStart seen left right)
    (second : ComparedOccurrenceTransport profile ready base bindings left right more lhs rhs) :
    ComparedOccurrenceTransport profile ready base bindings leftStart rightStart (seen ++ more) lhs rhs := by
  obtain ⟨checked, canonical, head, checkSeen, canonSeen, _⟩ := first
  obtain ⟨moreChecked, moreCanonical, tail, moreCheckSeen, moreCanonSeen, store⟩ := second
  have observed (front back : Trace grow sig) (frontSeen : PayloadPrefix.visible front = seen)
      (backSeen : PayloadPrefix.visible back = more) : PayloadPrefix.visible (front ++ back) = seen ++ more := by
    calc
      PayloadPrefix.visible (front ++ back) = PayloadPrefix.visible front ++ PayloadPrefix.visible back := List.filter_append ..
      _ = seen ++ more := by rw [frontSeen, backSeen]
  exact ⟨checked ++ moreChecked, canonical ++ moreCanonical, (transportAppend head tail).choose_spec.1,
    observed _ _ checkSeen moreCheckSeen, observed _ _ canonSeen moreCanonSeen, store⟩

theorem stationaryTransport {left right lhs rhs : Config (core3 grow) (HostState sig)}
    {checked canonical : Trace grow sig}
    (checkPath : ∀ place, Prefix profile ready (specDispatch ready base) left place checked lhs place)
    (canonPath : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place canonical rhs place) :
    OccurrenceTransport profile ready base bindings left right checked canonical lhs rhs := by
  refine ⟨id, ?_, ?_⟩
  · intro mark
    cases mark with
    | none => exact ⟨.absent (prefix_survives (checkPath (.active 0 0))).1,
        .absent (prefix_survives (canonPath (.active 0 0))).1⟩
    | some place => exact ⟨(checkPath place).toTrail, (canonPath place).toTrail⟩
  · intro older marks invariant place unmarked first second leftAt rightAt
    apply invariant place (by simpa only [List.nil_append, List.map_id] using unmarked) first second
    · exact (prefix_survives (checkPath place)).2.symm.trans leftAt
    · exact (prefix_survives (canonPath place)).2.symm.trans rightAt

theorem appendQuietCanonicalTransport {left right reached : Config (core3 grow) (HostState sig)}
    {labels : Trace grow sig}
    (history : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (read : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place labels reached place)
    (quiet : PayloadPrefix.visible labels = []) (same : left.store = reached.store) :
    ComparedOccurrenceTransport profile ready base bindings start incoming seen left reached := by
  simpa only [List.append_nil] using appendComparedTransport (more := []) history
    ⟨[], labels, stationaryTransport (fun place => .done left place) read, rfl, quiet, same⟩

private theorem append {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before middle after : Config (core3 grow) (HostState sig)} {leading trailing}
    (front : Steps profile ready dispatch before leading middle) (back : Steps profile ready dispatch middle trailing after) :
    Steps profile ready dispatch before (leading ++ trailing) after := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

private theorem unchangedOrGive {label}
    (step : Step profile ready (specDispatch ready base) start label finish) :
    UnchangedAt bindings start ∨ GiveInstall bindings (specDispatch ready base) start label finish := by
  classical
  cases step
  case call focused =>
    rename_i _ target _ _ _
    by_cases unchanged : Unchanged bindings target
    · left
      constructor
      · intro _ _ _ _ _ other
        have shape := other.symm.trans focused
        simp only [List.cons.injEq, Activation.mk.injEq, Focus.prog.injEq] at shape
        have programs := shape.1.2.1
        injection programs with operation _
        injection operation with same
        simpa only [same] using unchanged
      · intros; simp_all
    · exact .inr (.direct focused unchanged)
  case coreCallout focused calling =>
    rename_i _ _ _ _ _ callee args
    by_cases unchanged : Unchanged bindings (.hostCallout (E := core3 grow) callee args)
    · left
      constructor <;> intros <;> simp_all
    · exact .inr (.core focused calling unchanged)
  case' fault failed => cases failed
  all_goals (left; constructor <;> intros <;> simp_all [StepDefs.HostReadyCfg])
  all_goals
    have heads := (show (_ ∧ Prog.op (S := Eff (core3 grow) (HostState sig)) (α := Ret (core3 grow)) _ _ = Prog.op _ _ ∧ _) ∧ _
      from by assumption)
    have programs := heads.1.2.1
    injection programs with operation _
    cases operation

private theorem actualHostGet {thread resume frames rest label}
    (focused : start.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
    (step : Step profile ready (specDispatch ready base) start label finish) :
    label = .tau ∧ finish = { start with ctl := ⟨thread, .prog (resume start.host), frames⟩ :: rest } := by
  cases step
  case' fault failed => cases failed
  all_goals simp_all [StepDefs.HostReadyCfg]
  all_goals
    have heads := (show (_ ∧ Prog.op (S := Eff (core3 grow) (HostState sig)) (α := Ret (core3 grow)) _ _ = Prog.op _ _ ∧ _) ∧ _
      from by assumption)
    have programs := heads.1.2.1
    injection programs with operation continuation
    first
    | exact congrArg (fun next => next start.host) continuation
    | cases operation

private theorem ordinaryPeer {before next peer : Config (core3 grow) (HostState sig)} {label protectedReturn}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes before peer) (interior : HostFrame.InteriorFor protectedReturn before)
    (unchanged : UnchangedAt bindings before) (grows : CoreUpdateGrows before)
    (run : Step profile ready (specDispatch ready base) before label next) :
    ∃ after, Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer label after ∧
      HostFrame.Related.Paired changes next after := by
  have live : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) before label next := by
    rcases LiveDispatch.classify_step (bindings := bindings) run with live | install
    · exact live
    · cases install with
      | direct focused overlaid => exact (overlaid (unchanged.direct focused)).elim
      | core focused calling overlaid => exact (overlaid (unchanged.core focused calling)).elim
  obtain ⟨after, replay, aligned⟩ := HostFrame.Related.interior_step covers paired interior grows live
  cases replay with
  | cons _ step tail => cases tail; exact ⟨after, step, aligned⟩

theorem closedSyncRead (read : ClosedSyncReadyRead ready start) : ClosedHostRead start := by
  obtain ⟨task, inst, thread, frames, rest, focused, agrees⟩ := read
  refine ⟨thread, _, frames, rest, focused, fun other => ?_⟩
  exact congrArg (syncLiftCandidates task) (HostFrame.instCandidates_eq start.store inst (ready start.host) (ready other)
    (fun entry live candidate member suspended found blocked query condition =>
      agrees entry live candidate member suspended found blocked query condition other))

private theorem threadReadyClosed (store : CStore (core3 grow)) (thread : ThreadId) (left right : Nat → Bool)
    (closed : ∀ entry, store.thread? thread = some entry → entry.blocked = true →
      ∀ query, entry.readyCond ≠ some (.host query)) :
    store.threadReady left thread = store.threadReady right thread := by
  simp only [CStore.threadReady, CStore.threadIs]
  split
  · rename_i entry found
    unfold Thread.ready
    cases blocked : entry.blocked
    · rfl
    cases condition : entry.readyCond with
    | none => rfl
    | some predicate =>
      cases predicate <;> try rfl
      exact (closed entry found blocked _ condition).elim
  · rfl

theorem closedTickRead (next : List ThreadId → Session grow sig (Ret (core3 grow))) {thread frames rest}
    (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun host => next (start.store.candidates (ready host)))), frames⟩ :: rest)
    (closed : ∀ candidate ∈ start.store.waiting, ∀ entry, start.store.thread? candidate = some entry →
      entry.blocked = true → ∀ query, entry.readyCond ≠ some (.host query)) : ClosedHostRead start := by
  refine ⟨thread, _, frames, rest, focused, fun other => congrArg next ?_⟩
  exact List.filter_congr (fun candidate member => threadReadyClosed start.store candidate (ready start.host) (ready other)
    (closed candidate member))

theorem closedCancelRead (target : ThreadId) (next : Bool → Session grow sig (Ret (core3 grow))) {thread frames rest}
    (focused : start.ctl = ⟨thread, .prog (.op .hostGet (fun host => next (start.store.threadReady (ready host) target))), frames⟩ :: rest)
    (closed : ∀ entry, start.store.thread? target = some entry → entry.blocked = true →
      ∀ query, entry.readyCond ≠ some (.host query)) : ClosedHostRead start :=
  ⟨thread, _, frames, rest, focused, fun other => congrArg next
    (threadReadyClosed start.store target (ready start.host) (ready other) closed)⟩

theorem reachedClosedTickRead (enabled : StepDefs.HostReadyCfg start)
    (closed : let entered := StepDefs.enterHostSt start.store
      ∀ candidate ∈ entered.waiting, ∀ entry, entered.thread? candidate = some entry →
        entry.blocked = true → ∀ query, entry.readyCond ≠ some (.host query)) :
    ∃ atRead, Steps profile ready (specDispatch ready base) start [.host .tick, .tau, .tau] atRead ∧ ClosedHostRead atRead := by
  let entered := StepDefs.enterHostSt start.store
  let next : List ThreadId → Session grow sig (Ret (core3 grow)) := fun candidates => do
    match candidates with
    | [] => pure ()
    | first :: rest =>
      let chosen ← pickTick first rest
      Thread.resume chosen
    modifyStore StepDefs.leaveHostSt
    pure .unit
  let enteredState := { start with store := entered }
  let atRead := { enteredState with ctl := [Activation.ofProg none (.op .hostGet (fun host => next (entered.candidates (ready host))))] }
  exact ⟨atRead, .cons (.hostTick enabled) (.cons (.modify rfl) (.cons (.get rfl) (.refl _))), closedTickRead next rfl closed⟩

private theorem closedReadPeer {before peer : Config (core3 grow) (HostState sig)} {thread frames rest resume}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired changes before peer)
    (focus : before.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
    (agrees : ∀ host, resume before.host = resume host) :
    ∃ after, Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer .tau after ∧
      HostFrame.Related.Paired changes { before with ctl := ⟨thread,
        .prog (resume before.host), frames⟩ :: rest } after := by
  obtain ⟨peerFrames, peerRest, atPeer, aligned⟩ := paired.retarget focus (.prog (resume before.host)) before.host peer.host
  refine ⟨{ peer with ctl := ⟨thread, .prog (resume before.host), peerFrames⟩ :: peerRest }, ?_, aligned⟩
  rw [agrees peer.host]
  exact .hostGet atPeer

private theorem actualReplayDone {protectedReturn} (state : Config (core3 grow) (HostState sig)) :
    ActualCallbackReplay bindings profile ready base protectedReturn state [] state :=
  fun {_changes _retained peer mark} _ paired outside =>
    ⟨peer, mark, .refl _, paired, outside, .done _ _, .done _ _,
      (fun cursor => ⟨cursor, .done _ _, .done _ _⟩),
      id, (fun _ => ⟨.done _ _, .done _ _⟩), fun _ _ outside => by simpa only [List.map_id, List.nil_append] using outside⟩

private theorem actualReplayCons {before next after : Config (core3 grow) (HostState sig)} {label leading protectedReturn}
    (step : Step profile ready (specDispatch ready base) before label next)
    (matchStep : ∀ {changes peer}, (∀ first second, changes first second → protectedReturn first) →
      HostFrame.Related.Paired changes before peer →
      ∃ reached, Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer label reached ∧
        HostFrame.Related.Paired changes next reached)
    (tail : ActualCallbackReplay bindings profile ready base protectedReturn next leading after) :
    ActualCallbackReplay bindings profile ready base protectedReturn before (label :: leading) after := by
  intro changes retained peer mark covers paired outside
  obtain ⟨reached, live, aligned⟩ := matchStep covers paired
  have edit := pair_edit paired label
  have kept : Outside retained (segmentStorage next) (segmentStorage reached) (mark.bind (transitionEdit before label).follow) := by
    rw [step_edit step, step_edit live, ← edit]
    exact outside_edit outside _
  obtain ⟨last, finalMark, replay, final, finalOutside, left, right, _, move, tails, outsideTails⟩ := tail covers aligned kept
  let follow := fun cursor : Option Location => cursor.bind (transitionEdit before label).follow
  have trails : ∀ cursor, Trail profile ready (specDispatch ready base) before cursor (label :: leading) after (move (follow cursor)) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) peer cursor (label :: leading) last (move (follow cursor)) := by
    intro cursor
    obtain ⟨leftTrail, rightTrail⟩ := tails (follow cursor)
    exact ⟨.step step leftTrail, .step live (edit ▸ rightTrail)⟩
  refine ⟨last, finalMark, .cons live replay, final, finalOutside, .step step left, .step live (edit ▸ right),
    (fun cursor => ⟨_, trails cursor⟩), move ∘ follow, trails, ?_⟩
  intro older marks invariant
  have moved : OutsideMarks older (segmentStorage next) (segmentStorage reached) (marks.map follow) := by
    rw [step_edit step, step_edit live, ← edit]
    exact invariant.edit _
  simpa only [List.map_map] using outsideTails older _ moved

theorem classifyActual {protectedReturn} {labels : Trace grow sig}
    (run : Steps profile ready (specDispatch ready base) start labels finish) (includeComponentCalls : Bool := false)
    (includePoll : Bool := false) (includeWait : Bool := false) :
    ClassifiedCallbackRun bindings profile ready base protectedReturn start labels finish := by
  classical
  induction run with
  | refl state => exact .complete (.done state) (actualReplayDone state) (.refl state)
  | @cons before next after label trailing step tail ih =>
    have stop (cut : CallbackWorkerBoundary bindings ready (specDispatch ready base) protectedReturn before label next) :
        ClassifiedCallbackRun bindings profile ready base protectedReturn before (label :: trailing) after :=
      .boundary (leading := []) rfl (.done before) (.refl before) (actualReplayDone before) cut step tail
    by_cases component : includeComponentCalls = true ∧ ∃ active hostId caller resume frames rest,
        before.ctl = ⟨some active, .prog (.op (.call (.hostFunc hostId caller)) resume), frames⟩ :: rest
    · obtain ⟨_, _, _, _, _, _, _, focus⟩ := component
      exact stop (.componentInstall focus)
    by_cases poll : includePoll = true ∧ ∃ thread core resume frames rest mem inst args,
        before.ctl = ⟨thread, .core core resume, frames⟩ :: rest ∧
        (core3 grow).status before.store.core core = .callout (.builtin (.waitableSetPoll mem) inst) args
    · obtain ⟨_, _, _, _, _, _, _, _, _, focus, calling⟩ := poll
      exact stop (.pollInstall focus calling)
    by_cases wait : includeWait = true ∧ ∃ thread core resume frames rest mem inst args,
        before.ctl = ⟨thread, .core core resume, frames⟩ :: rest ∧
        (core3 grow).status before.store.core core = .callout (.builtin (.waitableSetWait mem) inst) args
    · obtain ⟨_, _, _, _, _, _, _, _, _, focus, calling⟩ := wait
      exact stop (.waitInstall focus calling)
    by_cases resumedWait : includeWait = true ∧
        ∃ waiter resumer afterResume frames rest core resume savedFrames mem entry,
          before.ctl = ⟨resumer, .prog (.op (.resumeThread waiter) afterResume), frames⟩ :: rest ∧
          before.cont? waiter = some ⟨some waiter, .prog (waitableWaitContinue mem entry), .core core resume :: savedFrames⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, focus, saved⟩ := resumedWait
      exact stop (.waitResume focus saved)
    by_cases closedRead : ClosedHostRead before
    · obtain ⟨thread, resume, frames, rest, focus, agrees⟩ := closedRead
      obtain ⟨rfl, rfl⟩ := actualHostGet focus step
      have grows : CoreUpdateGrows before := by simp [CoreUpdateGrows, focus]
      cases ih with
      | complete closed replay growing =>
        exact .complete (.closedRead focus agrees closed) (actualReplayCons step (fun _ paired => closedReadPeer paired focus agrees) replay)
          (.cons grows step growing)
      | @boundary leading _ _ _ _ split closed growing replay cut actual rest =>
        exact .boundary (leading := .tau :: leading) (congrArg (Label.tau :: ·) split) (.closedRead focus agrees closed)
          (.cons grows step growing) (actualReplayCons step (fun _ paired => closedReadPeer paired focus agrees) replay) cut actual rest
    rcases unchangedOrGive (bindings := bindings) step with unchanged | install
    · by_cases interior : HostFrame.InteriorFor protectedReturn before
      · by_cases noWrite : NoHostAssignment before
        · by_cases grows : CoreUpdateGrows before
          · have extend {leading reached}
                (closed : ClosedCallbackPrefix bindings profile ready base protectedReturn next (PayloadPrefix.visible leading) reached) :
                ClosedCallbackPrefix bindings profile ready base protectedReturn before (PayloadPrefix.visible (label :: leading)) reached := by
              change ClosedCallbackPrefix bindings profile ready base protectedReturn before (PayloadPrefix.visible ([label] ++ leading)) reached
              rw [show PayloadPrefix.visible ([label] ++ leading) = PayloadPrefix.visible [label] ++ PayloadPrefix.visible leading from List.filter_append ..]
              exact .step interior unchanged noWrite grows step closed
            cases ih with
            | complete closed replay growing =>
              exact .complete (extend closed) (actualReplayCons step (fun covers paired => ordinaryPeer covers paired interior unchanged grows step) replay)
                (.cons grows step growing)
            | boundary split closed growing replay cut actual rest =>
              exact .boundary (congrArg (label :: ·) split) (extend closed) (.cons grows step growing)
                (actualReplayCons step (fun covers paired => ordinaryPeer covers paired interior unchanged grows step) replay) cut actual rest
          · exact stop (.nonGrowingUpdate grows)
        · unfold NoHostAssignment at noWrite
          push Not at noWrite
          obtain ⟨_, _, _, _, _, focus⟩ := noWrite
          exact stop (.write focus)
      · unfold HostFrame.InteriorFor at interior
        rw [not_and_or] at interior
        push Not at interior
        rcases interior with ⟨_, _, _, _, focus⟩ | ⟨_, retained, _, _, _, _, focus⟩
        · exact stop (.read focus closedRead)
        · exact stop (.protectedPop retained focus)
    · exact stop (.give install)

theorem actualAllocatorPrefix {protectedReturn} {labels : Trace grow sig}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (replay : ActualCallbackReplay bindings profile ready base protectedReturn start labels finish)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes start incoming)
    (outside : Outside older (segmentStorage start) (segmentStorage incoming) (some (.active 0 0))) :
    ∃ reached mark, AllocatorMark profile ready base bindings older start incoming labels labels finish reached mark ∧
      HostFrame.Related.Paired changes finish reached ∧
      ComparedOccurrencePaths profile ready base bindings start incoming (PayloadPrefix.visible labels) finish reached := by
  obtain ⟨reached, mark, _, aligned, kept, left, right, tracks, _⟩ := replay covers paired outside
  exact ⟨reached, mark, ⟨kept, left, right, tracks⟩, aligned, labels, labels, tracks, rfl, rfl, aligned.data.1⟩

private theorem installTransport
    {checkEntry canonEntry peer : Config (core3 grow) (HostState sig)}
    {checkInstall canonInstall checkTrace canonTrace : Trace grow sig}
    {first second : Seg (core3 grow) (HostState sig)}
    (left : ∀ place, Prefix profile ready (specDispatch ready base) start place checkInstall checkEntry place.pushed)
    (right : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonInstall canonEntry place.pushed)
    (leftStorage : segmentStorage checkEntry = (Edit.push first).apply (segmentStorage start))
    (rightStorage : segmentStorage canonEntry = (Edit.push second).apply (segmentStorage incoming))
    {move : Option Location → Option Location}
    (trails : ∀ cursor, Trail profile ready (specDispatch ready base) checkEntry cursor checkTrace finish (move cursor) ∧
      Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonEntry cursor canonTrace peer (move cursor))
    (offMarks : ∀ retained marks, OutsideMarks retained (segmentStorage checkEntry) (segmentStorage canonEntry) marks →
      OutsideMarks retained (segmentStorage finish) (segmentStorage peer) (marks.map move)) :
    OccurrenceTransport profile ready base bindings start incoming (checkInstall ++ checkTrace) (canonInstall ++ canonTrace)
      finish peer [move (some (.active 0 0))] := by
  refine ⟨move ∘ (·.map Location.pushed), ?_, ?_⟩
  · intro place
    cases place with
    | none =>
      obtain ⟨lhs, rhs⟩ := trails none
      exact ⟨(Trail.absent (prefix_survives (left (.active 0 0))).1).append lhs,
        (Trail.absent (prefix_survives (right (.active 0 0))).1).append rhs⟩
    | some place =>
      obtain ⟨lhs, rhs⟩ := trails (some place.pushed)
      exact ⟨(left place).toTrail.append lhs, (right place).toTrail.append rhs⟩
  · intro retained marks olderFrames
    have installed := olderFrames.push first second
    rw [← leftStorage, ← rightStorage] at installed
    simpa only [List.map_cons, List.map_map, List.singleton_append] using offMarks retained _ installed

private theorem replayInstalledOccurrences {protectedReturn}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkInstall canonInstall : Trace grow sig}
    {first second : Seg (core3 grow) (HostState sig)}
    (left : ∀ place, Prefix profile ready (specDispatch ready base) start place checkInstall checkEntry place.pushed)
    (right : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonInstall canonEntry place.pushed)
    (leftStorage : segmentStorage checkEntry = (Edit.push first).apply (segmentStorage start))
    (rightStorage : segmentStorage canonEntry = (Edit.push second).apply (segmentStorage incoming))
    (initial : Outside older (segmentStorage checkEntry) (segmentStorage canonEntry) (some (.active 0 0)))
    (paired : HostFrame.Related.Paired changes checkEntry canonEntry)
    (covers : ∀ lhs rhs, changes lhs rhs → protectedReturn lhs)
    (replay : ActualCallbackReplay bindings profile ready base protectedReturn checkEntry seen finish) :
    ActualAllocatorOccurrencePrefix profile ready base bindings older changes start incoming checkEntry canonEntry
      checkInstall canonInstall seen finish := by
  obtain ⟨peer, _, _, aligned, _, _, _, _, move, trails, offMarks⟩ := replay covers paired
    (paired_outside (left := HostFrame.replace checkEntry canonEntry.host) paired)
  let mark := some (Location.active 0 0)
  obtain ⟨checkMark, canonMark⟩ := trails mark
  have kept : Outside older (segmentStorage finish) (segmentStorage peer) (move mark) := by
    apply outsideMarks_singleton.mp
    simpa only [List.nil_append, List.map_cons, List.map_nil] using offMarks older [mark] (outsideMarks_singleton.mpr initial)
  have marked : AllocatorMark profile ready base bindings older checkEntry canonEntry seen seen finish peer (move mark) :=
    ⟨kept, checkMark, canonMark, fun cursor => ⟨_, trails cursor⟩⟩
  exact ⟨peer, move mark, aligned, marked, installTransport left right leftStorage rightStorage trails
    (fun retained marks outside => by simpa only [List.nil_append] using offMarks retained marks outside)⟩

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

theorem unchangedTrail {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
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
      ∃ move : Option Location → Option Location, move mark = finalMark ∧
        (∀ cursor, Trail profile ready (specDispatch ready base) start cursor checkedLabels finish (move cursor) ∧
          Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming cursor canonLabels reached (move cursor)) ∧
        ∀ retained marks, OutsideMarks retained (segmentStorage start) (segmentStorage incoming) marks →
          OutsideMarks retained (segmentStorage finish) (segmentStorage reached) (marks.map move) := by
  induction path generalizing incoming mark with
  | done => exact ⟨[], [], incoming, mark, .refl _, .refl _, paired, rfl, rfl, .refl _, rfl, rfl, outside, .done _ _, .done _ _,
      id, rfl, (fun cursor => ⟨.done _ cursor, .done _ cursor⟩),
      fun _ _ invariant => by simpa only [List.map_id] using invariant⟩
  | @step current next last label rest interior unchanged noAssignment grows run _ ih =>
    obtain ⟨peer, peerStep, aligned⟩ := ordinaryPeer covers paired interior unchanged grows run
    have edit := pair_edit paired label
    have nextOutside : Outside older (segmentStorage next) (segmentStorage peer) (mark.bind (transitionEdit current label).follow) := by
      rw [step_edit run, step_edit peerStep, ← edit]
      exact outside_edit outside _
    obtain ⟨checkedLabels, canonLabels, reached, finalMark, checked, canonical, final, checkSeen, canonSeen, growth,
      checkRoots, canonRoots, finalOutside, checkTrail, canonTrail, move, movedMark, trails, transports⟩ := ih aligned nextOutside
    let follow := fun cursor : Option Location => cursor.bind (transitionEdit current label).follow
    refine ⟨_, _, reached, finalMark, .cons run checked, .cons peerStep canonical, final,
      (List.filter_append [_] checkedLabels).trans (congrArg (_ ++ ·) checkSeen),
      (List.filter_append [_] canonLabels).trans (congrArg (_ ++ ·) canonSeen),
      (CoreGrowthSteps.cons grows run (.refl _)).grows.trans growth,
      checkRoots.trans (congrArg (·.writer.accepted) (stepHost noAssignment run)),
      canonRoots.trans (congrArg (·.writer.accepted) (stepHost (noAssignmentPeer paired noAssignment) peerStep)),
      finalOutside, .step run checkTrail, .step peerStep (by rwa [← edit]), move ∘ follow, movedMark, ?_, ?_⟩
    · intro cursor
      obtain ⟨left, right⟩ := trails (follow cursor)
      exact ⟨.step run left, .step peerStep (edit ▸ right)⟩
    · intro retained marks invariant
      have moved : OutsideMarks retained (segmentStorage next) (segmentStorage peer) (marks.map follow) := by
        rw [step_edit run, step_edit peerStep, ← edit]
        exact invariant.edit _
      simpa only [List.map_map] using transports retained _ moved
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
      checkRoots, canonRoots, finalOutside, checkTrail, canonTrail, move, movedMark, trails, transports⟩ := ih aligned nextOutside
    have tau : (List.replicate count (.tau : Label (core3 grow) (HostState sig))).all (· matches .tau) = true := by
      apply List.all_eq_true.mpr
      intro label member
      rw [List.eq_of_mem_replicate member]
    refine ⟨_, _, reached, finalMark, append checked.steps checkTail, append canonical canonTail, final,
      (List.filter_append _ checkLabels).trans (by rw [← PayloadPrefix.visible, invisible tau, List.nil_append]; exact checkSeen),
      (List.filter_append _ canonLabels).trans (by rw [← PayloadPrefix.visible, invisible silent, List.nil_append]; exact canonSeen),
      growth, checkRoots, canonRoots.trans (congrArg (·.writer.accepted) host), finalOutside,
      (unchangedTrail checkedSlots mark).append checkTrail, (unchangedTrail canonSlots mark).append canonTrail, move, movedMark, ?_, ?_⟩
    · intro cursor
      obtain ⟨left, right⟩ := trails cursor
      exact ⟨(unchangedTrail checkedSlots cursor).append left, (unchangedTrail canonSlots cursor).append right⟩
    · intro retained marks invariant
      apply transports retained marks
      intro place offMarks first second leftAt rightAt
      exact invariant place offMarks first second
        ((prefix_survives (checkedSlots place)).2.symm.trans leftAt)
        ((prefix_survives (canonSlots place)).2.symm.trans rightAt)
  | @closedRead current _ _ thread frames rest resume focused agrees _ ih =>
    let residual := resume current.host
    obtain ⟨peerFrames, peerRest, atPeer, aligned⟩ := paired.retarget focused (.prog residual) current.host incoming.host
    have peerStep : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
        { incoming with ctl := ⟨thread, .prog residual, peerFrames⟩ :: peerRest } := by
      unfold residual
      rw [agrees incoming.host]
      exact .hostGet atPeer
    have nextOutside : Outside older
        (segmentStorage { current with ctl := ⟨thread, .prog residual, frames⟩ :: rest })
        (segmentStorage { incoming with ctl := ⟨thread, .prog residual, peerFrames⟩ :: peerRest }) mark := by
      simpa only [segmentStorage, focused, atPeer, List.map_cons, Activation.segs] using outside
    obtain ⟨_, _, reached, finalMark, checked, canonical, final, checkSeen, canonSeen, growth,
      checkRoots, canonRoots, finalOutside, checkTrail, canonTrail, move, movedMark, trails, transports⟩ := ih aligned nextOutside
    have unchanged (cursor : Option Location) : cursor.bind (Edit.same (E := core3 grow) (Host := HostState sig)).follow = cursor := by
      cases cursor with
      | none => rfl
      | some place => cases place <;> rfl
    refine ⟨_, _, reached, finalMark, .cons (.hostGet focused) checked, .cons peerStep canonical, final,
      checkSeen, canonSeen, growth, checkRoots, canonRoots, finalOutside, .step (.hostGet focused) ?_, .step peerStep ?_, move, movedMark, ?_, ?_⟩
    · rw [transitionEdit, focused]
      exact (unchanged mark).symm ▸ checkTrail
    · rw [transitionEdit, atPeer]
      exact (unchanged mark).symm ▸ canonTrail
    · intro cursor
      obtain ⟨left, right⟩ := trails cursor
      refine ⟨.step (.hostGet focused) ?_, .step peerStep ?_⟩
      · rw [transitionEdit, focused]
        exact (unchanged cursor).symm ▸ left
      · rw [transitionEdit, atPeer]
        exact (unchanged cursor).symm ▸ right
    · intro retained marks invariant
      apply transports retained marks
      simpa only [segmentStorage, focused, atPeer, List.map_cons, Activation.segs] using invariant

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

theorem appendExecutedCallbacks {middle peer last : Config (core3 grow) (HostState sig)}
    {checkLeading canonLeading checkTrailing canonTrailing : Trace grow sig}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (first : ExecutedCallbackSegment profile ready base bindings changes start incoming checkLeading canonLeading middle peer)
    (second : ExecutedCallbackSegment profile ready base bindings changes middle peer checkTrailing canonTrailing finish last) :
    ExecutedCallbackSegment profile ready base bindings changes start incoming
      (checkLeading ++ checkTrailing) (canonLeading ++ canonTrailing) finish last := by
  refine ⟨first.checkedRun.append second.checkedRun, ?_, second.paired,
    (transportAppend first.occurrences second.occurrences).choose_spec.1⟩
  simp only [PayloadPrefix.visible, List.filter_append]
  exact congrArg₂ List.append first.observed second.observed

theorem executeClassifiedPrefix {protectedReturn checkLabels}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (run : CoreGrowthSteps profile ready (specDispatch ready base) start checkLabels finish)
    (replay : ActualCallbackReplay bindings profile ready base protectedReturn start checkLabels finish)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes start incoming) :
    ∃ peer, ExecutedCallbackSegment profile ready base bindings changes start incoming checkLabels checkLabels finish peer := by
  obtain ⟨peer, _, _, aligned, _, _, _, _, movement⟩ := replay covers paired
    (paired_outside (left := HostFrame.replace start incoming.host) paired)
  exact ⟨peer, run, rfl, aligned, movement⟩

theorem compareReachedHostRead {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {thread resume frames rest label}
    (focus : start.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
    (step : Step profile ready (specDispatch ready base) start label finish)
    (paired : HostFrame.Related.Paired changes start incoming)
    (agrees : resume start.host = resume incoming.host) :
    ∃ peer, ExecutedCallbackSegment profile ready base bindings changes start incoming [label] [label] finish peer := by
  obtain ⟨rfl, rfl⟩ := actualHostGet focus step
  obtain ⟨peerFrames, peerRest, atPeer, aligned⟩ := paired.retarget focus (.prog (resume start.host)) start.host incoming.host
  let peer := { incoming with ctl := ⟨thread, .prog (resume start.host), peerFrames⟩ :: peerRest }
  have live : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau peer := by
    change Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
      { incoming with ctl := ⟨thread, .prog (resume start.host), peerFrames⟩ :: peerRest }
    rw [agrees]
    exact .hostGet atPeer
  refine ⟨peer, .cons (by simp [CoreUpdateGrows, focus]) (.hostGet focus) (.refl _), rfl, aligned, stationaryTransport ?_ ?_⟩
  · intro place
    refine .step (.hostGet focus) ?_ (.done _ _)
    rw [transitionEdit, focus]
    cases place <;> rfl
  · intro place
    refine .step live ?_ (.done _ _)
    rw [transitionEdit, atPeer]
    cases place <;> rfl

theorem compareDivergentHostRead {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {thread resume frames rest label middle trailing}
    (focus : start.ctl = ⟨thread, .prog (.op .hostGet resume), frames⟩ :: rest)
    (step : Step profile ready (specDispatch ready base) start label middle)
    (tail : Steps profile ready (specDispatch ready base) middle trailing finish)
    (paired : HostFrame.Related.Paired changes start incoming)
    (different : resume start.host ≠ resume incoming.host) :
    CallbackSliceEnd profile ready base bindings changes start incoming (label :: trailing) finish := by
  obtain ⟨rfl, rfl⟩ := actualHostGet focus step
  obtain ⟨peerFrames, peerRest, atPeer, _⟩ := paired.retarget focus (.prog (resume start.host)) start.host incoming.host
  refine .observation (otherNext := { incoming with ctl := ⟨thread, .prog (resume incoming.host), peerFrames⟩ :: peerRest })
    focus different (stationaryTransport ?_ ?_) tail
  · intro place
    refine .step (.hostGet focus) ?_ (.done _ _)
    rw [transitionEdit, focus]
    cases place <;> rfl
  · intro place
    refine .step (.hostGet atPeer) ?_ (.done _ _)
    rw [transitionEdit, atPeer]
    cases place <;> rfl

theorem compareReachedHostWrite {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {thread value resume frames rest}
    (focus : start.ctl = ⟨thread, .prog (.op (.hostSet value) resume), frames⟩ :: rest)
    (paired : HostFrame.Related.Paired changes start incoming) :
    ∃ peer, ExecutedCallbackSegment profile ready base bindings changes start incoming [.tau] [.tau]
      { start with host := value, ctl := ⟨thread, .prog (resume ()), frames⟩ :: rest } peer := by
  obtain ⟨peerFrames, peerRest, atPeer, aligned⟩ := paired.retarget focus (.prog (resume ())) value value
  refine ⟨_, .cons (by simp [CoreUpdateGrows, focus]) (.hostSet focus) (.refl _), rfl, aligned,
    stationaryTransport ?_ ?_⟩
  · intro place
    refine .step (.hostSet focus) ?_ (.done _ _)
    rw [transitionEdit, focus]
    cases place <;> rfl
  · intro place
    refine .step (.hostSet atPeer) ?_ (.done _ _)
    rw [transitionEdit, atPeer]
    cases place <;> rfl

theorem compareReachedJournalUpdate {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {thread read frames rest left right next}
    (focus : start.ctl = ⟨thread, .prog (.op .hostGet read), frames⟩ :: rest)
    (paired : HostFrame.Related.Paired changes start incoming)
    (checked : read start.host = .op (.hostSet left) (fun _ => next))
    (canonical : read incoming.host = .op (.hostSet right) (fun _ => next)) :
    ∃ peer, ExecutedCallbackSegment profile ready base bindings changes start incoming [.tau, .tau] [.tau, .tau]
      { start with host := left, ctl := ⟨thread, .prog next, frames⟩ :: rest } peer := by
  obtain ⟨peerFrames, peerRest, atPeer, aligned⟩ := paired.retarget focus (.prog next) left right
  have leftRead : Step profile ready (specDispatch ready base) start .tau
      { start with ctl := ⟨thread, .prog (.op (.hostSet left) (fun _ => next)), frames⟩ :: rest } := by
    rw [← checked]
    exact .hostGet focus
  have rightRead : Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
      { incoming with ctl := ⟨thread, .prog (.op (.hostSet right) (fun _ => next)), peerFrames⟩ :: peerRest } := by
    rw [← canonical]
    exact .hostGet atPeer
  refine ⟨_, .cons (by simp [CoreUpdateGrows, focus]) leftRead
    (.cons (by simp [CoreUpdateGrows]) (.hostSet rfl) (.refl _)), rfl, aligned, stationaryTransport ?_ ?_⟩
  · intro place
    refine .step (middle := place) leftRead ?_ (.step (.hostSet rfl) ?_ (.done _ _))
    · rw [transitionEdit, focus]
      cases place <;> rfl
    · cases place <;> rfl
  · intro place
    refine .step (middle := place) rightRead ?_ (.step (.hostSet rfl) ?_ (.done _ _))
    · rw [transitionEdit, atPeer]
      cases place <;> rfl
    · cases place <;> rfl

private theorem allocatorCallbackEvidence
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {index : CallbackPathIndex grow sig}
    (path : AllocatorCallbackPrefix profile ready base bindings older first second start incoming index seen finish)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (paired : HostFrame.Related.Paired (ReturnFrame.Extend older first second) start incoming) :
    ∃ checkLabels canonLabels reached,
      PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      Core3.Grows start.store.core finish.store.core ∧
      OccurrenceTransport profile ready base bindings start incoming checkLabels canonLabels finish reached ∧
      index.Matches checkLabels canonLabels reached := by
  cases path with
  | executed run => exact ⟨_, _, _, rfl, run.observed, run.paired, run.checkedRun.grows, run.occurrences, rfl⟩
  | closed path =>
    obtain ⟨checkLabels, canonLabels, reached, _, _, _, aligned, checkSeen, canonSeen, growth, _, _, _, _, _,
      move, _, trails, invariant⟩ := replayMarked path embedder (fun _ _ edge => by cases edge with
        | existing previous => exact .inl ⟨_, previous⟩
        | current => exact .inr rfl) paired (paired_outside (left := HostFrame.replace start incoming.host) paired)
    exact ⟨checkLabels, canonLabels, reached, checkSeen, canonSeen, aligned, growth, ⟨move, trails, invariant⟩, trivial⟩

private theorem throughAllocatorInstall
    {checkEntry canonEntry peer : Config (core3 grow) (HostState sig)}
    {checkInstall canonInstall checkLabels canonLabels : Trace grow sig}
    {first second : Seg (core3 grow) (HostState sig)}
    (left : ∀ place, Prefix profile ready (specDispatch ready base) start place checkInstall checkEntry place.pushed)
    (right : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place canonInstall canonEntry place.pushed)
    (leftStorage : segmentStorage checkEntry = (Edit.push first).apply (segmentStorage start))
    (rightStorage : segmentStorage canonEntry = (Edit.push second).apply (segmentStorage incoming))
    (initial : Outside older (segmentStorage checkEntry) (segmentStorage canonEntry) (some (.active 0 0)))
    (callback : OccurrenceTransport profile ready base bindings checkEntry canonEntry checkLabels canonLabels finish peer) :
    ∃ mark, AllocatorMark profile ready base bindings older checkEntry canonEntry checkLabels canonLabels finish peer mark ∧
      OccurrenceTransport profile ready base bindings start incoming (checkInstall ++ checkLabels) (canonInstall ++ canonLabels)
        finish peer [mark] := by
  obtain ⟨move, paths, invariant⟩ := callback
  let top : Option Location := some (.active 0 0)
  have outside := invariant older [top] (outsideMarks_singleton.mpr initial)
  exact ⟨move top, ⟨outsideMarks_singleton.mp outside, (paths top).1, (paths top).2, fun place => ⟨_, paths place⟩⟩,
    installTransport left right leftStorage rightStorage paths invariant⟩

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
          (PayloadPrefix.stringPlanResume cx steps canonNext)) checkedLabels canonLabels finish reached mark ∧
      OccurrenceTransport profile ready base bindings start incoming (.tau :: checkedLabels) (.tau :: canonLabels) finish reached [mark] := by
  obtain ⟨_, _, paired⟩ := frame.string_realloc_pair (profile := profile) (ready := ready) (bindings := bindings)
    cx ptr oldSize alignment size steps checkNext canonNext checkAt canonAt
  obtain ⟨checkedLabels, canonLabels, reached, mark, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots,
    outside, checkTrail, canonTrail, move, sameMark, trails, invariant⟩ :=
    replayMarked path embedder (fun _ _ edge => by cases edge with
      | existing previous => exact .inl ⟨_, previous⟩
      | current => exact .inr rfl) paired (frame.outside_installed (.pure .unit) (.pure .unit))
  have enterLeft := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    cx ptr oldSize alignment size steps checkNext start check checkAt
  have enterRight := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size steps canonNext incoming canon canonAt
  let first := PayloadPrefix.stringPlanResume cx steps checkNext
  let second := PayloadPrefix.stringPlanResume cx steps canonNext
  have leftEdit : transitionEdit start (.tau : Label (core3 grow) (HostState sig)) = Edit.push (.prog first) := by
    rw [transitionEdit, checkAt, PayloadPrefix.string_realloc_focus]
    rfl
  have rightEdit : transitionEdit incoming (.tau : Label (core3 grow) (HostState sig)) = Edit.push (.prog second) := by
    rw [transitionEdit, canonAt, PayloadPrefix.string_realloc_focus]
    rfl
  have pushed (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) (place : Location) :
      (Edit.push (.prog resume)).follow place = some place.pushed := by
    cases place with
    | active activation segment => cases activation <;> rfl
    | saved => rfl
  refine ⟨checkedLabels, canonLabels, reached, mark, .cons enterLeft checked, .cons enterRight canonical, final,
    checkSeen, canonSeen, growth, checkRoots, canonRoots, ⟨outside, checkTrail, canonTrail, fun place => ⟨_, trails place⟩⟩, ?_⟩
  rw [← sameMark]
  exact installTransport
    (fun place => .step enterLeft (leftEdit ▸ pushed first place) (.done _ _))
    (fun place => .step enterRight (rightEdit ▸ pushed second place) (.done _ _))
    (leftEdit ▸ step_edit enterLeft) (rightEdit ▸ step_edit enterRight) trails
    invariant

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
      ComparedOccurrencePaths profile ready base bindings start incoming seen finish reached ∧
      OccurrenceTransport profile ready base bindings start incoming ([.tau, .tau, .tau] ++ checkedLabels)
        ([.tau, .tau] ++ canonLabels) finish reached [mark] := by
  intro area first second path
  obtain ⟨_, _, paired⟩ := frame.collection_install_pair (profile := profile) (ready := ready) (bindings := bindings)
    destination inst type element entries output index checkNext canonNext width prepared checkAt canonAt
  have atCallback : HostFrame.Related.Paired (ReturnFrame.Extend older first second)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        incoming canon second) := paired
  obtain ⟨checkedLabels, canonLabels, reached, mark, checked, canonical, final, checkSeen, canonSeen, growth, checkRoots, canonRoots,
    outside, checkTrail, canonTrail, move, sameMark, trails, invariant⟩ :=
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
  have leftStorage : segmentStorage (PayloadPrefix.collectionEntry destination inst area entries.length
      (specDispatch ready base) start check first) = (Edit.push (.prog first)).apply (segmentStorage start) := by
    simp only [segmentStorage, checkAt, PayloadPrefix.collectionEntry, PayloadPrefix.Cursor.control, List.map_cons, Edit.apply, front]
    rfl
  have rightStorage : segmentStorage (PayloadPrefix.collectionEntry destination inst area entries.length
      (specDispatch ready (LiveDispatch.host bindings base)) incoming canon second) =
      (Edit.push (.prog second)).apply (segmentStorage incoming) := by
    simp only [segmentStorage, canonAt, PayloadPrefix.collectionEntry, PayloadPrefix.Cursor.control, List.map_cons, Edit.apply, front]
    rfl
  have transport := installTransport leftInstalls rightInstalls leftStorage rightStorage trails invariant
  refine ⟨checkedLabels, canonLabels, reached, mark, append enterLeft checked, append enterRight canonical, final,
    checkSeen, canonSeen, growth, checkRoots, canonRoots, ⟨outside, checkTrail, canonTrail, fun place => ⟨move place, trails place⟩⟩,
    ⟨_, _, transportPaths transport, checkSeen, canonSeen, (HostFrame.Related.Paired.data final).1⟩, sameMark ▸ transport⟩

open PayloadPrefix in
theorem actualStringInstall (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let first := stringPlanResume cx steps checkNext
    let second := stringPlanResume cx steps canonNext
    let checkEntry := LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check
    let canonEntry := stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size incoming canon second
    ActualCallbackReplay bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first) checkEntry seen finish →
    ActualAllocatorOccurrencePrefix profile ready base bindings older (ReturnFrame.Extend older first second) start incoming checkEntry canonEntry
      [.tau] [.tau] seen finish := by
  intro first second checkEntry canonEntry replay
  obtain ⟨_, _, paired⟩ := frame.string_realloc_pair (profile := profile) (ready := ready) (bindings := bindings)
    cx ptr oldSize alignment size steps checkNext canonNext checkAt canonAt
  have checked := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    cx ptr oldSize alignment size steps checkNext start check checkAt
  have canonical := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size steps canonNext incoming canon canonAt
  have leftEdit : transitionEdit start (.tau : Label (core3 grow) (HostState sig)) = Edit.push (.prog first) := by
    rw [transitionEdit, checkAt, PayloadPrefix.string_realloc_focus]
    rfl
  have rightEdit : transitionEdit incoming (.tau : Label (core3 grow) (HostState sig)) = Edit.push (.prog second) := by
    rw [transitionEdit, canonAt, PayloadPrefix.string_realloc_focus]
    rfl
  have pushed (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) (place : Location) :
      (Edit.push (.prog resume)).follow place = some place.pushed := by
    cases place with
    | active activation segment => cases activation <;> rfl
    | saved => rfl
  exact replayInstalledOccurrences
    (fun place => .step checked (leftEdit ▸ pushed first place) (.done _ _))
    (fun place => .step canonical (rightEdit ▸ pushed second place) (.done _ _))
    (leftEdit ▸ step_edit checked) (rightEdit ▸ step_edit canonical) (frame.outside_installed (.pure .unit) (.pure .unit)) paired
    (fun _ _ edge => by cases edge with
      | existing previous => exact .inl ⟨_, previous⟩
      | current => exact .inr rfl) replay

private theorem stringVisitorCallback (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {index : CallbackPathIndex grow sig} :
    let first := PayloadPrefix.stringPlanResume cx steps checkNext
    let second := PayloadPrefix.stringPlanResume cx steps canonNext
    let checkEntry := LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check
    let canonEntry := stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size incoming canon second
    AllocatorCallbackPrefix profile ready base bindings older first second checkEntry canonEntry index seen finish →
    ∃ checkLabels canonLabels reached mark,
      PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      Core3.Grows start.store.core finish.store.core ∧
      AllocatorMark profile ready base bindings older checkEntry canonEntry checkLabels canonLabels finish reached mark ∧
      OccurrenceTransport profile ready base bindings start incoming (.tau :: checkLabels) (.tau :: canonLabels) finish reached [mark] ∧
      index.Matches checkLabels canonLabels reached := by
  intro first second checkEntry canonEntry callback
  obtain ⟨_, _, paired⟩ := frame.string_realloc_pair (profile := profile) (ready := ready) (bindings := bindings)
    cx ptr oldSize alignment size steps checkNext canonNext checkAt canonAt
  obtain ⟨checkLabels, canonLabels, peer, checkSeen, canonSeen, aligned, growth, replay, exactPath⟩ :=
    allocatorCallbackEvidence callback embedder paired
  have checked := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
    cx ptr oldSize alignment size steps checkNext start check checkAt
  have canonical := PayloadPrefix.string_realloc_install (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size steps canonNext incoming canon canonAt
  have leftEdit : transitionEdit start (.tau : Label (core3 grow) (HostState sig)) = Edit.push (.prog first) := by
    rw [transitionEdit, checkAt, PayloadPrefix.string_realloc_focus]
    rfl
  have rightEdit : transitionEdit incoming (.tau : Label (core3 grow) (HostState sig)) = Edit.push (.prog second) := by
    rw [transitionEdit, canonAt, PayloadPrefix.string_realloc_focus]
    rfl
  have pushed (resume : ReturnFrame.Continuation (core3 grow) (HostState sig)) (place : Location) :
      (Edit.push (.prog resume)).follow place = some place.pushed := by
    cases place with
    | active activation _ => cases activation <;> rfl
    | saved => rfl
  obtain ⟨mark, tracked, movement⟩ := throughAllocatorInstall
    (fun place => .step checked (leftEdit ▸ pushed first place) (.done _ _))
    (fun place => .step canonical (rightEdit ▸ pushed second place) (.done _ _))
    (leftEdit ▸ step_edit checked) (rightEdit ▸ step_edit canonical) (frame.outside_installed (.pure .unit) (.pure .unit)) replay
  exact ⟨checkLabels, canonLabels, peer, mark, checkSeen, canonSeen, aligned, growth, tracked, movement, exactPath⟩

open PayloadPrefix in
theorem collectionVisitorCallback (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
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
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {pathIndex : CallbackPathIndex grow sig} :
    let area := layout destination.width element
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkEntry := collectionEntry destination inst area entries.length (specDispatch ready base) start check first
    let canonEntry := collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
      incoming canon second
    AllocatorCallbackPrefix profile ready base bindings older first second checkEntry canonEntry pathIndex seen finish →
    ∃ checkLabels canonLabels reached mark,
      PayloadPrefix.visible checkLabels = seen ∧ PayloadPrefix.visible canonLabels = seen ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      Core3.Grows start.store.core finish.store.core ∧
      AllocatorMark profile ready base bindings older checkEntry canonEntry checkLabels canonLabels finish reached mark ∧
      ComparedOccurrencePaths profile ready base bindings start incoming seen finish reached ∧
      OccurrenceTransport profile ready base bindings start incoming ([.tau, .tau, .tau] ++ checkLabels)
        ([.tau, .tau] ++ canonLabels) finish reached [mark] ∧ pathIndex.Matches checkLabels canonLabels reached := by
  intro area first second checkEntry canonEntry callback
  obtain ⟨_, _, paired⟩ := frame.collection_install_pair (profile := profile) (ready := ready) (bindings := bindings)
    destination inst type element entries output index checkNext canonNext width prepared checkAt canonAt
  obtain ⟨checkLabels, canonLabels, peer, checkSeen, canonSeen, aligned, growth, replay, exactPath⟩ :=
    allocatorCallbackEvidence callback embedder paired
  have checked := fun place => (PayloadPrefix.collection_install_occurrences (profile := profile) (ready := ready)
    (dispatch := specDispatch ready base) destination inst type element entries output index start incoming check canon
    checkNext canonNext width prepared checkAt canonAt place).1
  have canonical := fun place => (PayloadPrefix.collection_install_occurrences (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) destination inst type element entries output index
    start incoming check canon checkNext canonNext width prepared checkAt canonAt place).2
  have leftStorage : segmentStorage checkEntry = (Edit.push (.prog first)).apply (segmentStorage start) := by
    simp only [segmentStorage, checkAt, checkEntry, collectionEntry, Cursor.control, List.map_cons, Edit.apply, front]
    rfl
  have rightStorage : segmentStorage canonEntry = (Edit.push (.prog second)).apply (segmentStorage incoming) := by
    simp only [segmentStorage, canonAt, canonEntry, collectionEntry, Cursor.control, List.map_cons, Edit.apply, front]
    rfl
  obtain ⟨mark, tracked, movement⟩ := throughAllocatorInstall checked canonical leftStorage rightStorage
    (frame.outside_installed (.pure .unit) (.pure .unit)) replay
  exact ⟨checkLabels, canonLabels, peer, mark, checkSeen, canonSeen, aligned, growth, tracked,
    ⟨_, _, transportPaths movement, checkSeen, canonSeen, aligned.data.1⟩, movement, exactPath⟩

open PayloadPrefix in
theorem actualCollectionInstall (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
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
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkEntry := collectionEntry destination inst area entries.length (specDispatch ready base) start check first
    let canonEntry := collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base)) incoming canon second
    ActualCallbackReplay bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first) checkEntry seen finish →
    ActualAllocatorOccurrencePrefix profile ready base bindings older (ReturnFrame.Extend older first second) start incoming checkEntry canonEntry
      [.tau, .tau, .tau] [.tau, .tau] seen finish := by
  intro area first second checkEntry canonEntry replay
  obtain ⟨_, _, paired⟩ := frame.collection_install_pair (profile := profile) (ready := ready) (bindings := bindings)
    destination inst type element entries output index checkNext canonNext width prepared checkAt canonAt
  have checked := fun place => (PayloadPrefix.collection_install_occurrences (profile := profile) (ready := ready)
    (dispatch := specDispatch ready base) destination inst type element entries output index start incoming check canon
    checkNext canonNext width prepared checkAt canonAt place).1
  have canonical := fun place => (PayloadPrefix.collection_install_occurrences (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (LiveDispatch.host bindings base)) destination inst type element entries output index
    start incoming check canon checkNext canonNext width prepared checkAt canonAt place).2
  have leftStorage : segmentStorage checkEntry = (Edit.push (.prog first)).apply (segmentStorage start) := by
    simp only [segmentStorage, checkAt, checkEntry, collectionEntry, Cursor.control, List.map_cons, Edit.apply, front]
    rfl
  have rightStorage : segmentStorage canonEntry = (Edit.push (.prog second)).apply (segmentStorage incoming) := by
    simp only [segmentStorage, canonAt, canonEntry, collectionEntry, Cursor.control, List.map_cons, Edit.apply, front]
    rfl
  exact replayInstalledOccurrences checked canonical leftStorage rightStorage (frame.outside_installed (.pure .unit) (.pure .unit)) paired
    (fun _ _ edge => by cases edge with
      | existing previous => exact .inl ⟨_, previous⟩
      | current => exact .inr rfl) replay

theorem transportAllocatorPop {leftStart rightStart left right : Config (core3 grow) (HostState sig)}
    {checkTrace canonTrace : Trace grow sig} {value : Ret (core3 grow)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (leftAt : left.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
    (rightAt : right.ctl = { canon with frames := .prog second :: canon.frames }.control (.pure value))
    (paths : OccurrenceTransport profile ready base bindings leftStart rightStart checkTrace canonTrace left right [some (.active 0 0)]) :
    OccurrenceTransport profile ready base bindings leftStart rightStart (checkTrace ++ [.tau]) (canonTrace ++ [.tau])
      { left with ctl := check.control (first value) } { right with ctl := canon.control (second value) } := by
  obtain ⟨move, trails, invariant⟩ := paths
  let drop := fun mark : Option Location => mark.bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow
  refine ⟨drop ∘ move, ?_, ?_⟩
  · intro mark
    obtain ⟨lhs, rhs⟩ := trails mark
    exact ⟨lhs.append (Trail.pop_prog _ leftAt), rhs.append (Trail.pop_prog _ rightAt)⟩
  · intro retained marks previous
    have leftStep := Step.popProg (prof := profile) (hr := ready) (dispatch := specDispatch ready base) leftAt
    have rightStep := Step.popProg (prof := profile) (hr := ready)
      (dispatch := specDispatch ready (LiveDispatch.host bindings base)) rightAt
    have popLeft : transitionEdit left (.tau : Label (core3 grow) (HostState sig)) = .pop := by
      rw [transitionEdit, leftAt]
      rfl
    have popRight : transitionEdit right (.tau : Label (core3 grow) (HostState sig)) = .pop := by
      rw [transitionEdit, rightAt]
      rfl
    have leftStorage : segmentStorage { left with ctl := check.control (first value) } =
        (Edit.pop : Edit (core3 grow) (HostState sig)).apply (segmentStorage left) := by
      simpa only [PayloadPrefix.Cursor.control, popLeft] using step_edit leftStep
    have rightStorage : segmentStorage { right with ctl := canon.control (second value) } =
        (Edit.pop : Edit (core3 grow) (HostState sig)).apply (segmentStorage right) := by
      simpa only [PayloadPrefix.Cursor.control, popRight] using step_edit rightStep
    rw [leftStorage, rightStorage]
    have gone : (some (Location.active 0 0)).bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow = none := rfl
    simpa only [List.singleton_append, List.nil_append, List.map_cons, List.map_map, gone, outsideMarks_drop_lost]
      using (invariant retained marks previous).edit (.pop : Edit (core3 grow) (HostState sig))

theorem transportCoreCompletion {leftStart rightStart left right : Config (core3 grow) (HostState sig)}
    {checkTrace canonTrace : Trace grow sig} {reply : Event × List FlatValue}
    {thread core resume leftFrames rightFrames leftRest rightRest}
    (checkAt : left.ctl = ⟨thread, .prog (do return .flat (← writeCompletion reply)),
      .core core resume :: leftFrames⟩ :: leftRest)
    (canonAt : right.ctl = ⟨thread, .prog (.pure (.flat reply.2)),
      .core core resume :: rightFrames⟩ :: rightRest)
    (paths : OccurrenceTransport profile ready base bindings leftStart rightStart checkTrace canonTrace left right [some (.active 0 0)]) :
    OccurrenceTransport profile ready base bindings leftStart rightStart (checkTrace ++ [.tau, .tau, .tau]) (canonTrace ++ [.tau])
      { left with host := left.host.record reply.1
                  ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values reply.2)) resume, leftFrames⟩ :: leftRest }
      { right with ctl := ⟨thread, .core ((core3 grow).resume right.store.core core (.values reply.2)) resume, rightFrames⟩ :: rightRest } := by
  obtain ⟨move, trails, invariant⟩ := paths
  let drop := fun mark : Option Location => mark.bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow
  refine ⟨drop ∘ move, ?_, ?_⟩
  · intro mark
    obtain ⟨lhs, rhs⟩ := trails mark
    cases atMark : move mark with
    | none =>
      rw [atMark] at lhs rhs
      simp only [Function.comp_apply, atMark]
      exact ⟨lhs.append (.absent (Plain.give_completion_steps reply checkAt)),
        rhs.append (.absent (.cons (.popCore canonAt) (.refl _)))⟩
    | some place =>
      rw [atMark] at lhs rhs
      simp only [Function.comp_apply, atMark]
      exact ⟨lhs.append (Plain.give_completion_trail reply place checkAt), rhs.append (Trail.pop_core place canonAt)⟩
  · intro retained marks previous
    have leftStorage : segmentStorage
        { left with host := left.host.record reply.1
                    ctl := ⟨thread, .core ((core3 grow).resume left.store.core core (.values reply.2)) resume, leftFrames⟩ :: leftRest } =
        (Edit.pop : Edit (core3 grow) (HostState sig)).apply (segmentStorage left) := by
      simp only [segmentStorage, checkAt, Edit.apply, front, List.map_cons, List.headD_cons, List.tail_cons]
    have rightStorage : segmentStorage
        { right with ctl := ⟨thread, .core ((core3 grow).resume right.store.core core (.values reply.2)) resume, rightFrames⟩ :: rightRest } =
        (Edit.pop : Edit (core3 grow) (HostState sig)).apply (segmentStorage right) := by
      simp only [segmentStorage, canonAt, Edit.apply, front, List.map_cons, List.headD_cons, List.tail_cons]
    rw [leftStorage, rightStorage]
    have gone : (some (Location.active 0 0)).bind (Edit.pop : Edit (core3 grow) (HostState sig)).follow = none := rfl
    simpa only [List.singleton_append, List.nil_append, List.map_cons, List.map_map, gone, outsideMarks_drop_lost]
      using (invariant retained marks previous).edit (.pop : Edit (core3 grow) (HostState sig))

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
        { finish with ctl := check.control (first value) } { incoming with ctl := canon.control (second value) } ∧
      incoming.ctl = { canon with frames := .prog second :: canon.frames }.control (.pure value) := by
  obtain ⟨place, eq, trail⟩ := marked.canonicalTrail.survives
  cases eq
  have atTop := (prefix_survives trail).2.trans installed
  obtain ⟨canon, frame, canonAt⟩ := LinkedCallback.marked_pop_frame paired marked.outside returning atTop
  obtain ⟨checkPlace, checkEq, checkTrail⟩ := marked.checkedTrail.survives
  cases checkEq
  refine ⟨canon, frame, .popProg returning, .popProg canonAt, ?_, ?_, ?_, canonAt⟩
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

theorem localLeafTransport {Result : Type} {store : CStore (core3 grow)}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {leftHost rightHost : HostState sig}
    {checkNext canonNext : Result → Session grow sig (Ret (core3 grow))} {result : Except TrapReason Result}
    {checked canonical : Trace grow sig}
    (paths : let lhs := localLeafEnd left leftHost store check.thread check.frames check.rest checkNext result
      let rhs := localLeafEnd right rightHost store canon.thread canon.frames canon.rest canonNext result
      ∀ mark, Trail profile ready (specDispatch ready base) left mark checked lhs (localOccurrenceEnd result mark) ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) right mark canonical rhs (localOccurrenceEnd result mark)) :
    OccurrenceTransport profile ready base bindings left right checked canonical
      (localLeafEnd left leftHost store check.thread check.frames check.rest checkNext result)
      (localLeafEnd right rightHost store canon.thread canon.frames canon.rest canonNext result) := by
  refine ⟨localOccurrenceEnd result, paths, ?_⟩
  intro older marks invariant place unmarked first second leftAt rightAt
  have keeps (kept : localOccurrenceEnd result (some place) = some place) : ReturnFrame.Related.Segment older first second := by
    have oldUnmarked : some place ∉ marks := fun found =>
      unmarked (List.mem_map.mpr ⟨some place, found, kept⟩)
    obtain ⟨left, right⟩ := paths (some place)
    rw [kept] at left right
    obtain ⟨leftPlace, leftEq, left⟩ := left.survives
    obtain ⟨rightPlace, rightEq, right⟩ := right.survives
    have leftPlaceEq := Option.some.inj leftEq
    have rightPlaceEq := Option.some.inj rightEq
    subst leftPlace rightPlace
    exact invariant place oldUnmarked first second ((prefix_survives left).2.symm.trans leftAt)
      ((prefix_survives right).2.symm.trans rightAt)
  cases result with
  | ok => exact keeps rfl
  | error => cases place with
    | saved => exact keeps rfl
    | active => simp [localLeafEnd, StepDefs.trapCfg, segmentStorage, segmentAt] at leftAt

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
    refine ⟨store, result, labels, observed, checked, canonical, localLeafTransport trails, ?_⟩
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
      let action : StoreStep := oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)
      let lhs := { left with store, ctl := check.control (runStoreSteps cx ptr (action :: rest) >>= checkNext) }
      let rhs := { right with store, ctl := canon.control (runStoreSteps cx ptr (action :: rest) >>= canonNext) }
      have middle : LinkedCallback.ChildFrameOver older lhs rhs check canon :=
        ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨_, _, installed⟩ := middle.string_realloc_pair (profile := profile) (ready := ready) (bindings := bindings)
          cx ptr oldSize alignment size rest checkNext canonNext rfl rfl
        exact ⟨.cons (PayloadPrefix.string_realloc_install cx ptr oldSize alignment size rest checkNext lhs check rfl) (.refl _),
          .cons (PayloadPrefix.string_realloc_install cx ptr oldSize alignment size rest canonNext rhs canon rfl) (.refl _), installed⟩
      intro index seen reached path
      obtain ⟨checkLabels, canonLabels, reference, mark, checkSeen, canonSeen, paired,
        callGrowth, marked, installed, exactPath⟩ := stringVisitorCallback (profile := profile) (ready := ready)
        cx ptr oldSize alignment size rest checkNext canonNext middle rfl rfl embedder path
      obtain ⟨_, leftRun, rightRun⟩ := transportPaths installed none
      refine ⟨checkLabels, canonLabels, reference, mark, leftRun.steps, rightRun.steps, checkSeen, canonSeen, paired,
        callGrowth, marked, installed, exactPath, ?_⟩
      intro value cursor atMark returning
      cases atMark
      obtain ⟨peer, residual, _, _, leftPop, rightPop, _, referenceAt⟩ := pop marked paired returning rfl
      refine ⟨peer, ?_, ?_, ?_, ?_⟩
      · exact fun depth => (stringInstallTracks _ cx ptr oldSize alignment size rest checkNext lhs check rfl depth).append
          (leftPop depth)
      · exact fun depth => (stringInstallTracks _ cx ptr oldSize alignment size rest canonNext rhs canon rfl depth).append
          (rightPop depth)
      · exact transportAllocatorPop returning referenceAt installed
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
      refine ⟨matched.1, ?_⟩
      intro index seen reached path
      obtain ⟨checkLabels, canonLabels, reference, mark, lhs, rhs, checkSeen, canonSeen, paired,
        growth, marked, trails, exactPath, returning⟩ := matched.2 path
      refine ⟨checkLabels, canonLabels, reference, mark, lhs, rhs, checkSeen, canonSeen, paired,
        growth, marked, trails, exactPath, ?_⟩
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

theorem appendQuietCanonicalRead {leftStart rightStart left right reached : Config (core3 grow) (HostState sig)}
    {seen labels : Trace grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left right)
    (tracks : ∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) right place labels reached place)
    (quiet : PayloadPrefix.visible labels = []) (same : left.store = reached.store) :
    ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left reached := by
  have result := appendComparedOccurrences (after := []) leading
    ⟨[], labels, fun mark => ⟨mark, .done _ _, unchangedTrail tracks mark⟩, rfl, quiet, same⟩
  simpa only [List.append_nil] using result

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

theorem locatedLocalPaths {Result : Type} {keep : CStore (core3 grow) → Prop}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext : Result → Session grow sig (Ret (core3 grow))} {offset : Nat}
    {visit : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (cut : PayloadPrefix.LocalCutKeepingBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) keep left right check canon checkNext canonNext true)
    (next : ∀ words observed lhs rhs,
      keep lhs.store → LinkedCallback.ChildFrameOver older lhs rhs check canon →
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset →
      lhs.ctl = check.control (checkNext words) → rhs.ctl = canon.control (canonNext words) → visit observed lhs rhs check canon) :
    LocatedLocalPathsThen profile ready base bindings start incoming left right seen offset visit := by
  obtain ⟨store, result, checked, canonical, lhs, rhs, matched, outcome, trails⟩ := cut
  have paths : ComparedOccurrencePaths profile ready base bindings left right (PayloadPrefix.visible canonical)
      (localLeafEnd left left.host store check.thread check.frames check.rest checkNext result)
      (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result) :=
    ⟨checked, canonical, transportPaths (localLeafTransport trails), matched, rfl, by cases result <;> rfl⟩
  cases result with
  | error reason =>
    obtain ⟨prior, trap⟩ := outcome
    exact .inl ⟨reason, prior, _, _, appendComparedPaths leading
      ⟨checked, canonical, lhs, rhs.steps, matched.trans trap, trap, rfl⟩, trap ▸ paths, rfl, rfl⟩
  | ok words =>
    obtain ⟨kept, checkTracks, canonTracks⟩ := outcome
    have reached := appendComparedSlots leading ⟨checked, canonical, checkTracks, canonTracks, matched, rfl⟩
    exact .inr ⟨PayloadPrefix.visible canonical, _, _, check, canon, reached, paths,
      next words _ _ _ kept ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ reached rfl rfl⟩


theorem localCutOccurrences {Result : Type} {keep : CStore (core3 grow) → Prop}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext : Result → Session grow sig (Ret (core3 grow))}
    {visit : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (cut : PayloadPrefix.LocalCutKeepingBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) keep left right check canon checkNext canonNext true)
    (next : ∀ words observed lhs rhs,
      keep lhs.store → LinkedCallback.ChildFrameOver older lhs rhs check canon →
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs →
      lhs.ctl = check.control (checkNext words) → rhs.ctl = canon.control (canonNext words) → visit observed lhs rhs check canon) :
    LocalOccurrenceThen profile ready base bindings start incoming seen visit := by
  obtain ⟨store, result, checked, canonical, _, _, matched, outcome, trails⟩ := cut
  have paths : ComparedOccurrencePaths profile ready base bindings left right (PayloadPrefix.visible canonical)
      (localLeafEnd left left.host store check.thread check.frames check.rest checkNext result)
      (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result) :=
    ⟨checked, canonical, transportPaths (localLeafTransport trails), matched, rfl, by cases result <;> rfl⟩
  cases result with
  | error reason =>
    obtain ⟨prior, trap⟩ := outcome
    exact .inl ⟨reason, prior, _, _, appendComparedOccurrences leading (trap ▸ paths), rfl, rfl⟩
  | ok words =>
    obtain ⟨kept, _, _⟩ := outcome
    have reached := appendComparedOccurrences leading paths
    exact .inr ⟨PayloadPrefix.visible canonical, _, _, check, canon, reached,
      next words _ _ _ kept ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ reached rfl rfl⟩

theorem localCutTransport {Result : Type} {keep : CStore (core3 grow) → Prop}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext canonNext : Result → Session grow sig (Ret (core3 grow))}
    {visit : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (cut : PayloadPrefix.LocalCutKeepingBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) keep left right check canon checkNext canonNext true)
    (next : ∀ words observed lhs rhs,
      keep lhs.store → LinkedCallback.ChildFrameOver older lhs rhs check canon →
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      lhs.ctl = check.control (checkNext words) → rhs.ctl = canon.control (canonNext words) → visit observed lhs rhs check canon) :
    LocalTransportThen profile ready base bindings start incoming seen visit := by
  obtain ⟨store, result, checked, canonical, _, _, matched, outcome, trails⟩ := cut
  have transported : ComparedOccurrenceTransport profile ready base bindings left right (PayloadPrefix.visible canonical)
      (localLeafEnd left left.host store check.thread check.frames check.rest checkNext result)
      (localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext result) :=
    ⟨checked, canonical, localLeafTransport trails, matched, rfl, by cases result <;> rfl⟩
  cases result with
  | error reason =>
    obtain ⟨prior, trap⟩ := outcome
    exact .inl ⟨reason, prior, _, _, appendComparedTransport leading (trap ▸ transported), rfl, rfl⟩
  | ok words =>
    obtain ⟨kept, _, _⟩ := outcome
    have reached := appendComparedTransport leading transported
    exact .inr ⟨PayloadPrefix.visible canonical, _, _, check, canon, reached,
      next words _ _ _ kept ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩ reached rfl rfl⟩

theorem rebaseLocatedLocalPaths {left right : Config (core3 grow) (HostState sig)} {offset : Nat}
    {visit : Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (cut : LocatedLocalPathsThen profile ready base bindings start incoming left right seen offset visit) :
    (∃ reason prior lhs rhs,
      ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ (prior ++ [.trap reason])) lhs rhs ∧
      lhs.ctl = [] ∧ rhs.ctl = []) ∨
    (∃ more lhs rhs check canon,
      ComparedSlots profile ready base bindings start incoming (seen ++ more) lhs rhs offset ∧
      ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ more) lhs rhs ∧
      visit (seen ++ more) lhs rhs check canon) := by
  rcases cut with ⟨reason, prior, lhs, rhs, _, localPath, lhsTrap, rhsTrap⟩ |
    ⟨more, lhs, rhs, check, canon, active, localPath, next⟩
  · exact .inl ⟨reason, prior, lhs, rhs, appendComparedOccurrences leading localPath, lhsTrap, rhsTrap⟩
  · exact .inr ⟨more, lhs, rhs, check, canon, active, appendComparedOccurrences leading localPath, next⟩

theorem stringOccurrencesFrom {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {leftStart rightStart left right : Config (core3 grow) (HostState sig)}
    {ends : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    {finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    {length : Nat} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {leftBody rightBody : Config (core3 grow) (HostState sig)}
    (leading : ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left right)
    (incomingTransport : ∃ bodySeen, ComparedOccurrenceTransport profile ready base bindings leftBody rightBody bodySeen left right)
    (run : LiveStringReplay profile ready base bindings older cx checkNext canonNext ends length left right check canon)
    (next : ∀ pointer observed lhs rhs cursor peer, ends pointer lhs rhs cursor peer →
      ComparedOccurrencePaths profile ready base bindings leftStart rightStart observed lhs rhs →
      (∃ bodySeen, ComparedOccurrenceTransport profile ready base bindings leftBody rightBody bodySeen lhs rhs) →
      finish pointer observed lhs rhs cursor peer) :
    LiveStringOccurrences profile ready base bindings older cx checkNext canonNext leftStart rightStart finish
      length left right check canon seen leftBody rightBody := by
  induction length using Nat.strong_induction_on generalizing left right check canon seen with
  | ind length ih =>
    rw [LiveStringReplay] at run
    rw [LiveStringOccurrences]
    obtain ⟨store, result, labels, observed, _, _, localTrails, nextCut⟩ := run
    obtain ⟨bodySeen, checked, canonical, prefixTransport, checkView, canonView, shared⟩ := incomingTransport
    have localTransport := (transportAppend prefixTransport localTrails).choose_spec.1
    have localHistory := appendComparedTransport ⟨checked, canonical, prefixTransport, checkView, canonView, shared⟩
      ⟨labels, labels, localTrails, rfl, rfl, by cases result <;> rfl⟩
    have reached := appendComparedOccurrences leading ⟨labels, labels, transportPaths localTrails, rfl, rfl, by cases result <;> rfl⟩
    refine ⟨store, result, labels, observed, reached, ⟨_, _, localTransport⟩, ?_⟩
    cases result with
    | error => exact ⟨rfl, rfl⟩
    | ok front =>
      obtain ⟨_, _, matched⟩ := nextCut front rfl
      have silent : PayloadPrefix.visible labels = [] := visibleLeaf observed
      rw [silent, List.append_nil] at reached
      cases front with
      | done => exact next _ _ _ _ _ _ matched (by simpa only [silent, List.append_nil] using reached) ⟨_, localHistory⟩
      | call ptr oldSize alignment size rest shorter =>
        refine ⟨matched.1, ?_⟩
        intro index observed reachedCall path
        obtain ⟨checkLabels, canonLabels, reference, mark, _, _, checkSeen, canonSeen, paired,
          _, marked, movement, exactPath, returning⟩ := matched.2 path
        have sameStore := (HostFrame.Related.Paired.data paired).1
        have suspended := (transportAppend localTransport movement).choose_spec.1
        refine ⟨checkLabels, canonLabels, reference, mark, marked, paired,
          appendComparedOccurrences reached ⟨_, _, transportPaths movement, checkSeen, canonSeen, sameStore⟩,
          ⟨_, _, by simpa only [List.map_nil, List.append_nil] using suspended⟩, exactPath, ?_⟩
        intro value cursor atMark focus
        obtain ⟨peer, _, _, returned, residual⟩ := returning value cursor atMark focus
        have silentPop (raw : Trace grow sig) (observedAs : PayloadPrefix.visible raw = observed) :
            PayloadPrefix.visible (.tau :: raw ++ [.tau]) = observed := by
          change PayloadPrefix.visible (raw ++ [.tau]) = observed
          rw [show PayloadPrefix.visible (raw ++ [.tau]) = PayloadPrefix.visible raw ++
            PayloadPrefix.visible ([.tau] : Trace grow sig) from List.filter_append .., observedAs]
          simp [PayloadPrefix.visible]
        have afterPop := appendComparedOccurrences reached
          ⟨_, _, transportPaths returned, silentPop _ checkSeen, silentPop _ canonSeen, sameStore⟩
        have resumed := appendComparedTransport localHistory ⟨_, _, returned, silentPop _ checkSeen, silentPop _ canonSeen, sameStore⟩
        exact ⟨peer, afterPop, ih rest.length shorter afterPop ⟨_, resumed⟩ residual⟩

theorem stringOccurrences {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {leftStart rightStart left right : Config (core3 grow) (HostState sig)}
    {ends : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    {finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    {length : Nat} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {seen : Trace grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings leftStart rightStart seen left right)
    (run : LiveStringReplay profile ready base bindings older cx checkNext canonNext ends length left right check canon)
    (next : ∀ pointer observed lhs rhs cursor peer, ends pointer lhs rhs cursor peer →
      ComparedOccurrencePaths profile ready base bindings leftStart rightStart observed lhs rhs →
      finish pointer observed lhs rhs cursor peer) :
    LiveStringOccurrences profile ready base bindings older cx checkNext canonNext leftStart rightStart finish
      length left right check canon seen := by
  apply stringOccurrencesFrom leading _ run (fun pointer observed lhs rhs cursor peer done paths _ =>
    next pointer observed lhs rhs cursor peer done paths)
  obtain ⟨_, _, _, _, _, shared⟩ := leading
  refine ⟨[], [], [], ⟨id, (fun mark => ⟨.done _ mark, .done _ mark⟩), ?_⟩, rfl, rfl, shared⟩
  intro _ _ invariant
  simpa only [List.nil_append, List.map_id] using invariant

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

private theorem replayBetweenPathsWith {mode : LinkedCallback.MemorySequence.Track} {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {entries : List Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {sink : RefusalSink grow sig}
    {history : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop}
    (lift : LiftsFieldPathsWith history child paths sink)
    (leading : history seen left right)
    (advance : ∀ {observed lhs rhs reached labels}, history observed lhs rhs → PayloadPrefix.visible labels = [] →
      (∀ place, Prefix profile ready (specDispatch ready (LiveDispatch.host bindings base)) rhs place labels reached place) →
      lhs.store = reached.store →
      history observed lhs reached)
    (same : left.store = right.store)
    (run : LinkedCallback.MemorySequence.ReplayBetween profile ready (specDispatch ready (LiveDispatch.host bindings base))
      mode destination inst child checkNext canonNext finish entries index address left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      history observed lhs rhs → lhs.store = rhs.store →
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
    have reached := advance leading quiet read same
    have occurrenceCut : ComparedOccurrencePaths profile ready base bindings left right [] left
        (LinkedCallback.MemorySequence.focus mode destination inst item address right canon
          (LinkedCallback.MemorySequence.canonTail mode destination inst rest (mode.slot destination.width item address).2 canonNext)) :=
      ⟨[], _, fun mark => ⟨mark, .done _ _, unchangedTrail read mark⟩, rfl, quiet, same⟩
    exact ⟨occurrenceCut, lift _ _ _ _ _ _ _ _ _ _ _ _ body reached same admitted
      (fun _ _ _ _ _ tracks shared tail => ih tracks shared tail)⟩

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
  refine replayBetweenPathsWith lift leading ?_ same run admitted next
  intro observed lhs rhs reached labels history quiet read _
  simpa only [List.append_nil] using appendComparedSlots (after := []) history
    ⟨[], labels, (fun _ => .done _ _), (fun depth => read (.active 0 depth)), rfl, quiet⟩

theorem replayBetweenOccurrencePathsFrom {mode : LinkedCallback.MemorySequence.Track} {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {entries : List Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {sink : RefusalSink grow sig}
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (same : left.store = right.store)
    (run : LinkedCallback.MemorySequence.ReplayBetween profile ready (specDispatch ready (LiveDispatch.host bindings base))
      mode destination inst child checkNext canonNext finish entries index address left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    replayBetweenPaths profile ready base bindings mode destination inst paths checkNext canonNext visit
      entries index address seen left right check canon := by
  refine replayBetweenPathsWith lift leading ?_ same run admitted next
  intro observed lhs rhs reached labels history quiet read shared
  simpa only [List.append_nil] using appendComparedOccurrences (after := []) history
    ⟨[], labels, fun mark => ⟨mark, .done _ _, unchangedTrail read mark⟩, rfl, quiet, shared⟩

theorem replayBetweenTransportFrom {mode : LinkedCallback.MemorySequence.Track} {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {entries : List Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {sink : RefusalSink grow sig}
    (lift : LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LinkedCallback.MemorySequence.ReplayBetween profile ready (specDispatch ready (LiveDispatch.host bindings base))
      mode destination inst child checkNext canonNext finish entries index address left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    replayBetweenPaths profile ready base bindings mode destination inst paths checkNext canonNext visit
      entries index address seen left right check canon := by
  have shared := leading.choose_spec.choose_spec.2.2.2
  refine replayBetweenPathsWith lift leading ?_ shared run admitted next
  intro observed lhs rhs reached labels history quiet read same
  simpa only [List.append_nil] using appendComparedTransport (more := []) history
    ⟨[], labels, stationaryTransport (fun place => .done lhs place) read, rfl, quiet, same⟩

theorem liveElementsPathsFrom {destination : RecordDestination} {inst : InstId} {stride : Nat}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {entries : List Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {sink : RefusalSink grow sig}
    {history : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop}
    (lift : LiftsFieldPathsWith history child paths sink)
    (leading : history seen left right)
    (same : left.store = right.store)
    (run : liveElements destination inst stride child checkNext canonNext finish entries index address left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      history observed lhs rhs → lhs.store = rhs.store →
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
        refine ⟨matched.1, ?_⟩
        intro index observed reachedCall path
        obtain ⟨checkLabels, canonLabels, reference, mark, _, _, checkSeen, canonSeen, paired,
          _, marked, _, exactPath, returning⟩ := matched.2 path
        have sameStore := HostFrame.Related.Paired.data paired |>.1
        have live := allocatorPaths
          (stringInstallTracks _ cx ptr oldSize alignment size rest checkNext _ check rfl)
          (stringInstallTracks _ cx ptr oldSize alignment size rest canonNext _ canon rfl)
          marked checkSeen canonSeen sameStore
        refine ⟨checkLabels, canonLabels, reference, mark, marked, paired, appendAllocatorPaths reached live, exactPath, ?_⟩
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
  have reached := appendComparedSlots leading ⟨checkLabels, canonLabels, fun depth => checkEntry (.active 0 depth),
    fun depth => canonEntry (.active 0 depth), checkSeen, canonSeen⟩
  rw [List.append_nil] at reached
  exact stringPaths next reached body

theorem stringValueOccurrencePathsFrom {destination : RecordDestination} {inst : InstId} {key : LinkedCallback.StringField}
    {output : Stored.Lower.Output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {ends : Nat → LinkedCallback.MemorySequence.Finish grow sig}
    {finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    {leftBody rightBody : Config (core3 grow) (HostState sig)}
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (movement : ∃ bodySeen, ComparedOccurrenceTransport profile ready base bindings leftBody rightBody bodySeen left right)
    (run : StringValueThen profile ready base bindings older destination inst key output left right check canon checkNext canonNext ends)
    (next : ∀ pointer observed lhs rhs cursor peer, ends pointer lhs rhs cursor peer →
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs →
      (∃ bodySeen, ComparedOccurrenceTransport profile ready base bindings leftBody rightBody bodySeen lhs rhs) →
      finish pointer observed lhs rhs cursor peer) :
    StringValueOccurrencePaths profile ready base bindings older destination inst key output start incoming left right check canon
      checkNext canonNext finish seen leftBody rightBody := by
  obtain ⟨checkLabels, canonLabels, checkSeen, canonSeen, checkEntry, canonEntry, frame, body⟩ := run
  have entry : ComparedOccurrenceTransport profile ready base bindings left right [] _ _ :=
    ⟨checkLabels, canonLabels, stationaryTransport checkEntry canonEntry, checkSeen, canonSeen, frame.store⟩
  obtain ⟨bodySeen, history⟩ := movement
  refine stringOccurrencesFrom (seen := seen) ?_ ⟨bodySeen ++ [], appendComparedTransport history entry⟩ body next
  simpa only [List.append_nil] using appendComparedOccurrences (after := []) leading (comparedTransportPaths entry)

theorem stringValueOccurrencePaths {destination : RecordDestination} {inst : InstId} {key : LinkedCallback.StringField}
    {output : Stored.Lower.Output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output}
    {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {ends : Nat → LinkedCallback.MemorySequence.Finish grow sig}
    {finish : Nat → Trace grow sig → LinkedCallback.MemorySequence.Finish grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : StringValueThen profile ready base bindings older destination inst key output left right check canon checkNext canonNext ends)
    (next : ∀ pointer observed lhs rhs cursor peer, ends pointer lhs rhs cursor peer →
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → finish pointer observed lhs rhs cursor peer) :
    StringValueOccurrencePaths profile ready base bindings older destination inst key output start incoming left right check canon
      checkNext canonNext finish seen := by
  have shared : left.store = right.store := by
    obtain ⟨_, _, _, _, _, shared⟩ := leading
    exact shared
  exact stringValueOccurrencePathsFrom leading ⟨[], [], [], stationaryTransport (fun place => .done left place)
    (fun place => .done right place), rfl, rfl, shared⟩ run
    (fun pointer observed lhs rhs cursor peer done paths _ => next pointer observed lhs rhs cursor peer done paths)

theorem localFieldPaths {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig} {offset : Nat}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : LiveLocalFieldThen profile ready base bindings checkNext canonNext finish left right check canon)
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocatedLocalPathsThen profile ready base bindings start incoming left right seen offset visit := by
  obtain ⟨store, result, lhsLabels, rhsLabels, lhs, rhs, same, trails, cut⟩ := run
  cases result with
  | error reason =>
    obtain ⟨before, trapped⟩ := cut
    exact .inl ⟨reason, before, _, _, appendComparedPaths leading
      ⟨lhsLabels, rhsLabels, lhs, rhs, same.trans trapped, trapped, rfl⟩,
      ⟨lhsLabels, rhsLabels, transportPaths trails, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok value =>
    cases value
    obtain ⟨lhsTrack, rhsTrack, done⟩ := cut
    have reached := appendComparedSlots leading ⟨lhsLabels, rhsLabels, lhsTrack, rhsTrack, rfl, same.symm⟩
    exact .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, reached,
      ⟨lhsLabels, rhsLabels, transportPaths trails, rfl, same.symm, rfl⟩, next _ _ _ _ _ reached rfl done⟩

private theorem localFieldOccurrences {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : LiveLocalFieldThen profile ready base bindings checkNext canonNext finish left right check canon)
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalOccurrenceThen profile ready base bindings start incoming seen visit := by
  obtain ⟨store, result, lhsLabels, rhsLabels, _, _, same, trails, cut⟩ := run
  cases result with
  | error reason =>
    obtain ⟨before, trapped⟩ := cut
    exact .inl ⟨reason, before, _, _, appendComparedOccurrences leading
      ⟨lhsLabels, rhsLabels, transportPaths trails, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok value =>
    cases value
    have reached := appendComparedOccurrences leading ⟨lhsLabels, rhsLabels, transportPaths trails, rfl, same.symm, rfl⟩
    exact .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, reached, next _ _ _ _ _ reached rfl cut.2.2⟩

theorem localFieldTransport {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveLocalFieldThen profile ready base bindings checkNext canonNext finish left right check canon)
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalTransportThen profile ready base bindings start incoming seen visit := by
  obtain ⟨store, result, lhsLabels, rhsLabels, _, _, same, trails, cut⟩ := run
  cases result with
  | error reason =>
    obtain ⟨before, trapped⟩ := cut
    exact .inl ⟨reason, before, _, _, appendComparedTransport leading
      ⟨lhsLabels, rhsLabels, trails, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok value =>
    cases value
    have reached := appendComparedTransport leading ⟨lhsLabels, rhsLabels, trails, rfl, same.symm, rfl⟩
    exact .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, reached, next _ _ _ _ _ reached rfl cut.2.2⟩

theorem handleValueOccurrences {item : Field} {index : Nat} {output : Stored.Lower.Output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output} {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {finish : output.Result → LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (same : left.store = right.store)
    (run : LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index output left right check canon checkNext canonNext
      finish)
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    HandleOccurrenceThen profile ready base bindings start incoming left right seen item index check checkNext visit sink := by
  unfold LinkedCallback.HandleFieldThenBetween at run
  cases decision : liveLeafPlan left.store left.host.writer index item with
  | error issue =>
    rw [decision] at run
    obtain ⟨labels, tau, retained⟩ := run
    have silent := invisible (List.all_eq_true.mpr (fun label member => by rw [tau label member]))
    have reached := appendComparedOccurrences (after := []) leading
      ⟨labels, [], fun mark => ⟨mark, unchangedTrail retained mark, .done _ _⟩, silent, rfl, same⟩
    rw [List.append_nil] at reached
    exact .inl ⟨issue, decision, reached, covers _ admitted issue _ _ _ check rfl reached⟩
  | ok plan =>
    rw [decision] at run
    obtain ⟨store, result, guard, lhsLabels, rhsLabels, tau, lhsKind, rhsKind, _, _, trails, continued⟩ := run
    have silent : PayloadPrefix.visible guard = [] :=
      invisible (List.all_eq_true.mpr (fun label member => by rw [tau label member]))
    have lhsSeen := (List.filter_append ..).trans (congrArg₂ List.append silent (visibleLeaf lhsKind))
    cases result with
    | error reason =>
      exact .inr (.inl ⟨reason, [], _, _, appendComparedOccurrences leading
        ⟨_, _, fun mark => ⟨_, trails mark⟩, lhsSeen, visibleLeaf rhsKind, rfl⟩, rfl, rfl⟩)
    | ok result =>
      obtain ⟨_, _, done⟩ := continued result rfl
      have reached := appendComparedOccurrences leading ⟨_, _, fun mark => ⟨_, trails mark⟩, lhsSeen, visibleLeaf rhsKind, rfl⟩
      exact .inr (.inr ⟨[], _, _, check, canon, reached, next result _ _ _ _ _ reached rfl done⟩)


theorem handleValueTransport {item : Field} {index : Nat} {output : Stored.Lower.Output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.ValueCheckNext grow sig output} {canonNext : LinkedCallback.MemorySequence.ValueCanonNext grow sig output}
    {finish : output.Result → LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index output left right check canon checkNext canonNext finish)
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    HandleTransportThen profile ready base bindings start incoming left right seen item index check checkNext visit sink := by
  unfold LinkedCallback.HandleFieldThenBetween at run
  cases decision : liveLeafPlan left.store left.host.writer index item with
  | error issue =>
    rw [decision] at run
    obtain ⟨labels, tau, retained⟩ := run
    have silent := invisible (List.all_eq_true.mpr (fun label member => by rw [tau label member]))
    have reached := appendComparedTransport (more := []) leading
      ⟨labels, [], stationaryTransport retained (fun place => .done right place), silent, rfl,
        leading.choose_spec.choose_spec.2.2.2⟩
    rw [List.append_nil] at reached
    exact .inl ⟨issue, decision, reached, covers _ admitted issue _ _ _ check rfl (comparedTransportPaths reached)⟩
  | ok plan =>
    rw [decision] at run
    obtain ⟨store, result, guard, lhsLabels, rhsLabels, tau, lhsKind, rhsKind, _, _, trails, continued⟩ := run
    have silent : PayloadPrefix.visible guard = [] :=
      invisible (List.all_eq_true.mpr (fun label member => by rw [tau label member]))
    have lhsSeen := (List.filter_append ..).trans (congrArg₂ List.append silent (visibleLeaf lhsKind))
    have movement := localLeafTransport trails
    cases result with
    | error reason =>
      exact .inr (.inl ⟨reason, [], _, _, appendComparedTransport leading
        ⟨_, _, movement, lhsSeen, visibleLeaf rhsKind, rfl⟩, rfl, rfl⟩)
    | ok result =>
      obtain ⟨_, _, done⟩ := continued result rfl
      have reached := appendComparedTransport (more := []) leading ⟨_, _, movement, lhsSeen, visibleLeaf rhsKind, rfl⟩
      exact .inr (.inr ⟨[], _, _, check, canon, reached, next result _ _ _ _ _ reached rfl done⟩)

private theorem handleFieldOccurrences {item : Field} {index address : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (same : left.store = right.store)
    (run : LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base)
      (specDispatch ready (LiveDispatch.host bindings base)) item index (.memory address) left right check canon checkNext canonNext
      (fun () => finish))
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    HandleOccurrenceThen profile ready base bindings start incoming left right seen item index check checkNext visit sink :=
  handleValueOccurrences leading same run covers admitted (fun () => next)

theorem leafOccurrenceLift {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf} {sink : RefusalSink grow sig}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming) (leaf : TrailLeafType type) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (leafOccurrencePaths profile ready base bindings older destination inst start incoming sink type) sink := by
  rcases leaf with nominal | data | rfl
  · cases nominal <;> intro _ _ _ _ _ _ _ _ _ _ _ _ run leading same admitted next <;>
      exact handleFieldOccurrences leading same run covers admitted next
  · cases data with
    | @primitive primitive nonstring =>
      cases primitive <;> first
        | exact (nonstring rfl).elim
        | intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ _ next; exact localFieldOccurrences leading run next
    | enum | flags =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ _ next
      exact localFieldOccurrences leading run next
  · intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ _ next
    obtain ⟨str, field, body⟩ := run
    exact ⟨str, field, stringValueOccurrencePaths leading body
      (fun _ _ _ _ _ _ descriptor reached => localFieldOccurrences reached descriptor next)⟩

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
        checkNext canonNext (fun _ observed lhs rhs _ _ =>
          LocatedLocalPathsThen profile ready base bindings start incoming lhs rhs observed offset visit) seen offset := by
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
    have reached := appendComparedSlots leading ⟨labels, [], fun depth => retained (.active 0 depth), fun _ => .done _ _, silent, rfl⟩
    rw [List.append_nil] at reached
    refine .inl ⟨issue, decision, reached, ⟨labels, [], ?_, silent, rfl, same⟩, covers _ admitted issue seen _ _ check rfl same reached⟩
    intro mark
    refine ⟨mark, ?_, .done _ _⟩
    cases mark with
    | none => exact Trail.absent (prefix_survives (retained (.active 0 0))).1
    | some place => exact (retained place).toTrail
  | ok plan =>
    rw [decision] at run
    obtain ⟨store, result, guard, lhsLabels, rhsLabels, tau, lhsKind, rhsKind, lhsRun, rhsRun, trails, continued⟩ := run
    have silent : PayloadPrefix.visible guard = [] :=
      invisible (List.all_eq_true.mpr (fun label member => by rw [tau label member]))
    have lhsSeen := (List.filter_append ..).trans (congrArg₂ List.append silent (visibleLeaf lhsKind))
    cases result with
    | error reason =>
      exact .inr (.inl ⟨reason, [], _, _, appendComparedPaths leading
        ⟨_, _, lhsRun, rhsRun, lhsSeen, visibleLeaf rhsKind, rfl⟩,
        ⟨_, _, fun mark => ⟨_, trails mark⟩, lhsSeen, visibleLeaf rhsKind, rfl⟩, rfl, rfl⟩)
    | ok result =>
      obtain ⟨lhsTrack, rhsTrack, done⟩ := continued result rfl
      have reached := appendComparedSlots leading ⟨_, _, lhsTrack, rhsTrack, lhsSeen, visibleLeaf rhsKind⟩
      exact .inr (.inr ⟨[], _, _, check, canon, reached,
        ⟨_, _, fun mark => ⟨_, trails mark⟩, lhsSeen, visibleLeaf rhsKind, rfl⟩, next result _ _ _ _ _ reached rfl done⟩)

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
    {paths : Stored.TypeOf → TrailFieldComparison grow sig} {sink : RefusalSink grow sig}
    {history : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop}
    (lift : ∀ type raw, (type, raw) ∈ comparisons → LiftsFieldPathsWith history raw (paths type) sink) :
    LiftsFieldPathsWith history (aggregateChild comparisons) (selectFieldPaths paths) sink := by
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
  have reached := appendComparedSlots (after := []) leading
    ⟨[.tau], [], (fun depth => read (.active 0 depth)), (fun _ => .done _ _), rfl, rfl⟩
  rw [List.append_nil] at reached
  exact ⟨⟨[.tau], [], fun mark => ⟨mark, unchangedTrail read mark, .done _ _⟩, rfl, rfl, same⟩,
    replayBetweenPathsFrom lift reached same body (sink.nested _ admitted index) next⟩

theorem recordTable (destination : RecordDestination) (inst : InstId) (fields : List (String × Stored.TypeOf)) :
    liveRecordFields profile ready base bindings older destination inst fields =
      liveTupleFields profile ready base bindings older destination inst (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    cases field
    simp only [liveRecordFields, List.map_cons, liveTupleFields, ih]

theorem aggregateOccurrencePathsFrom {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {items : List Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {sink : RefusalSink grow sig}
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (same : left.store = right.store)
    (run : LiveAggregateThen profile ready base bindings destination inst child items index address checkNext canonNext finish
      left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveAggregatePaths profile ready base bindings destination inst paths items index address checkNext canonNext visit
      seen left right check canon := by
  obtain ⟨read, body⟩ := run
  have placement : ComparedOccurrencePaths profile ready base bindings left right []
      (LinkedCallback.MemorySequence.enterAggregate destination inst items index address left check checkNext) right :=
    ⟨[.tau], [], fun mark => ⟨mark, unchangedTrail read mark, .done _ _⟩, rfl, rfl, same⟩
  have reached := appendComparedOccurrences leading placement
  rw [List.append_nil] at reached
  exact ⟨placement, replayBetweenOccurrencePathsFrom lift reached same body (sink.nested _ admitted index) next⟩

private theorem tupleFieldOccurrenceLift {destination : RecordDestination} {inst : InstId} {types : List Stored.TypeOf}
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (leaves : ∀ type ∈ types, TrailLeafType type) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (aggregateChild (liveTupleFields profile ready base bindings older destination inst types))
      (selectFieldPaths (leafOccurrencePaths profile ready base bindings older destination inst start incoming sink)) sink := by
  apply aggregateChildLift
  intro type raw member
  induction types with
  | nil => cases member
  | cons schema rest ih =>
    rw [liveTupleFields] at member
    rcases List.mem_cons.mp member with equal | later
    · cases equal
      exact leafOccurrenceLift covers (leaves _ (List.mem_cons_self ..))
    · exact ih (fun item present => leaves item (List.mem_cons_of_mem _ present)) later

theorem leafAggregateOccurrenceLift {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf}
    {sink : RefusalSink grow sig} (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (leaves : TrailLeafAggregate type) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (aggregateFieldPaths profile ready base bindings destination inst type
        (leafOccurrencePaths profile ready base bindings older destination inst start incoming sink)) sink := by
  cases leaves with
  | @record fields declared =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨items, aligned, body⟩ := run
    rw [recordTable destination inst] at body
    have types : ∀ field ∈ fields.map Prod.snd, TrailLeafType field := by
      intro type member
      obtain ⟨field, inFields, rfl⟩ := List.mem_map.mp member
      exact declared field inFields
    exact ⟨items, aligned, aggregateOccurrencePathsFrom (tupleFieldOccurrenceLift covers types) leading same body admitted next⟩
  | tuple declared =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨items, aligned, body⟩ := run
    exact ⟨items, aligned, aggregateOccurrencePathsFrom (tupleFieldOccurrenceLift covers declared) leading same body admitted next⟩

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
    LocatedLocalPathsThen profile ready base bindings start incoming left right seen offset
      (match selected with
      | none => visit
      | some item => paths item 0 (PayloadPrefix.sumPayloadAddress destination.width arms address)
          (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext visit) := by
  obtain ⟨store, result, lhsLabels, rhsLabels, lhsRun, rhsRun, same, trails, tail⟩ := run
  cases result with
  | error reason =>
    obtain ⟨prefixLabels, trapped⟩ := tail
    exact .inl ⟨reason, prefixLabels, _, _, appendComparedPaths leading
      ⟨lhsLabels, rhsLabels, lhsRun, rhsRun, same.trans trapped, trapped, rfl⟩,
      ⟨lhsLabels, rhsLabels, transportPaths trails, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok result =>
    cases result
    obtain ⟨lhsTrack, rhsTrack, done⟩ := tail
    have reached := appendComparedSlots leading ⟨lhsLabels, rhsLabels, lhsTrack, rhsTrack, rfl, same.symm⟩
    refine .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, reached,
      ⟨lhsLabels, rhsLabels, transportPaths trails, rfl, same.symm, rfl⟩, ?_⟩
    cases selected with
    | none => exact next _ _ _ _ _ reached rfl done
    | some item =>
      exact lift rfl item 0 _ _ _ check canon _ canonNext finish visit _ done reached rfl
        (sink.nested _ admitted index) next

theorem sumOccurrencePathsFrom {destination : RecordDestination} {inst : InstId}
    {child : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig}
    {arms : List (Option Stored.TypeOf)} {selected : Option Field} {index address : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {sink : RefusalSink grow sig}
    (lift : selected.isSome = true → LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : LiveSumThen profile ready base bindings destination inst child arms selected index address
      checkNext canonNext finish left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalOccurrenceThen profile ready base bindings start incoming seen
      (match selected with
      | none => visit
      | some item => paths item 0 (PayloadPrefix.sumPayloadAddress destination.width arms address)
          (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext visit) := by
  obtain ⟨store, result, lhsLabels, rhsLabels, _, _, same, trails, tail⟩ := run
  cases result with
  | error reason =>
    obtain ⟨prefixLabels, trapped⟩ := tail
    exact .inl ⟨reason, prefixLabels, _, _, appendComparedOccurrences leading
      ⟨lhsLabels, rhsLabels, transportPaths trails, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok result =>
    cases result
    obtain ⟨_, _, done⟩ := tail
    have reached := appendComparedOccurrences leading ⟨lhsLabels, rhsLabels, transportPaths trails, rfl, same.symm, rfl⟩
    refine .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, reached, ?_⟩
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
  obtain ⟨store, result, labels, kind, lhsRun, rhsRun, _, tail⟩ := descriptors
  cases result with
  | error reason =>
    have trace : PayloadPrefix.visible labels = [.trap reason] := visibleLeaf kind
    exact .inl ⟨reason, [], _, _, appendComparedPaths path ⟨labels, labels, lhsRun.steps, rhsRun.steps, trace, trace, rfl⟩, rfl, rfl⟩
  | ok result =>
    cases result
    obtain ⟨lhsTrack, rhsTrack, widthRead, widthSilent, widthTrack, valueRun⟩ := tail
    have silent : PayloadPrefix.visible labels = [] := visibleLeaf kind
    have reached := appendComparedSlots path ⟨labels, labels ++ widthRead, lhsTrack,
      fun depth => (rhsTrack depth).append (widthTrack (.active 0 depth)), silent,
      (List.filter_append ..).trans (congrArg₂ List.append silent widthSilent)⟩
    exact .inr ⟨[], _, _, cursor, peer, reached, rfl, next _ _ _ _ _ _ reached rfl valueRun⟩

theorem stringMapEntryOccurrences {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {output : Stored.Lower.Output} {field value : Field} {index slot : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {compare : LinkedCallback.MemorySequence.FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : TrailFinish grow sig} {sink : RefusalSink grow sig}
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming compare paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : LiveStringMapEntryThen profile ready base bindings older destination inst element output
      field value index slot compare checkNext canonNext finish left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    stringMapEntryOccurrencePaths profile ready base bindings older destination inst element output start incoming paths
      field value index slot checkNext canonNext visit seen left right check canon := by
  obtain ⟨key, keyField, body⟩ := run
  refine ⟨key, keyField, stringValueOccurrencePaths leading body ?_⟩
  intro pointer observed lhs rhs cursor peer descriptors history
  obtain ⟨store, result, labels, kind, _, _, occurrences, tail⟩ := descriptors
  cases result with
  | error reason =>
    have traps : PayloadPrefix.visible labels = [.trap reason] := visibleLeaf kind
    exact .inl ⟨reason, [], _, _, appendComparedOccurrences history
      ⟨labels, labels, transportPaths occurrences, traps, traps, rfl⟩, rfl, rfl⟩
  | ok result =>
    cases result
    obtain ⟨_, _, widthRead, widthSilent, widthTracks, valueRun⟩ := tail
    have quiet : PayloadPrefix.visible labels = [] := visibleLeaf kind
    have descriptorPath := appendComparedOccurrences (after := []) history
      ⟨labels, labels, transportPaths occurrences, quiet, quiet, rfl⟩
    have reached := appendQuietCanonicalRead descriptorPath widthTracks widthSilent rfl
    exact .inr ⟨[], _, _, cursor, peer, reached,
      lift value 1 _ _ _ cursor peer _ canonNext finish visit _ valueRun reached rfl (sink.nested _ admitted index) next⟩

theorem stringMapEntryTransport {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {output : Stored.Lower.Output} {field value : Field} {index slot : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {compare : LinkedCallback.MemorySequence.FieldComparison grow sig}
    {checkNext : LinkedCallback.MemorySequence.CheckNext grow sig} {canonNext : LinkedCallback.MemorySequence.CanonNext grow sig}
    {finish : LinkedCallback.MemorySequence.Finish grow sig} {visit : Nat → TrailFinish grow sig}
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveStringMapEntryThen profile ready base bindings older destination inst element output
      field value index slot compare checkNext canonNext finish left right check canon)
    (next : ∀ ptr observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      compare value 1 ptr lhs rhs cursor peer (LinkedCallback.MemorySequence.aggregateNext index checkNext) canonNext finish →
      visit ptr observed lhs rhs cursor peer) :
    StringMapEntryTransport profile ready base bindings older destination inst element output start incoming visit
      field value index slot checkNext canonNext seen left right check canon := by
  obtain ⟨key, keyField, body⟩ := run
  refine ⟨key, keyField, stringValueOccurrencePathsFrom (comparedTransportPaths leading) ⟨seen, leading⟩ body ?_⟩
  intro pointer observed lhs rhs cursor peer descriptors _ transported
  obtain ⟨bodySeen, history⟩ := transported
  obtain ⟨store, result, labels, kind, _, _, movement, tail⟩ := descriptors
  cases result with
  | error reason =>
    have trapped : PayloadPrefix.visible labels = [.trap reason] := visibleLeaf kind
    exact .inl ⟨bodySeen, reason, _, _, appendComparedTransport history ⟨labels, labels, movement, trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok valueDone =>
    cases valueDone
    obtain ⟨_, _, widthRead, widthSilent, widthTracks, valueRun⟩ := tail
    have quiet : PayloadPrefix.visible labels = [] := visibleLeaf kind
    have written := appendComparedTransport (more := []) history ⟨labels, labels, movement, quiet, quiet, rfl⟩
    have reached := appendComparedTransport (more := []) written
      ⟨[], widthRead, stationaryTransport (fun place => .done _ place) widthTracks, rfl, widthSilent, rfl⟩
    exact .inr ⟨_, _, _, reached, next _ _ _ _ _ _ reached valueRun⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
