module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.WriterPaths

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
variable {ready : HostReady (HostState sig)} {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
variable {start middle finish incoming peer target left right : Config (core3 grow) (HostState sig)}
variable {labels leading trailing checked canonical canonLeading canonTrailing actual : Trace grow sig}
variable {before after changes : List (WriterChange sig)} {updates : List Stored.OwnedMemory.Claims.Spend}

theorem ofSteps (run : Steps profile ready dispatch start labels finish) :
    ∃ changes, WriterPath profile ready dispatch start labels finish changes := by
  classical
  induction run with
  | refl state => exact ⟨[], .done state⟩
  | @cons start next _ _ _ step _ ih =>
    obtain ⟨changes, tail⟩ := ih
    by_cases same : next.host.writer = start.host.writer
    · exact ⟨changes, .same step same tail⟩
    · exact ⟨_, .changed step same tail⟩

theorem append (first : WriterPath profile ready dispatch start leading middle before)
    (rest : WriterPath profile ready dispatch middle trailing finish after) :
    WriterPath profile ready dispatch start (leading ++ trailing) finish (before ++ after) := by
  induction first with
  | done => exact rest
  | same step unchanged _ ih => exact .same step unchanged (ih rest)
  | changed step different _ ih => exact .changed step different (ih rest)

theorem spend (path : WriterPath profile ready dispatch start labels finish changes)
    (spends : List.Forall₂ WriterChange.IsSpend changes updates) :
    finish.host.writer = updates.foldl (fun state update => update.apply state) start.host.writer := by
  induction path generalizing updates with
  | done => cases spends; rfl
  | same _ unchanged _ ih => simpa only [unchanged] using ih spends
  | changed _ _ _ ih =>
    cases spends with
    | cons head tail =>
      have after : _ = _ := head.2
      rw [List.foldl_cons, ← after]
      exact ih tail

theorem firstChange {change : WriterChange sig}
    (path : WriterPath profile ready dispatch start labels finish (change :: changes)) :
    ∃ leading label trailing before after, labels = leading ++ label :: trailing ∧
      WriterPath profile ready dispatch start leading before [] ∧
      Step profile ready dispatch before label after ∧
      change = (before.host.writer, after.host.writer) ∧ after.host.writer ≠ before.host.writer ∧
      WriterPath profile ready dispatch after trailing finish changes := by
  generalize effectList : change :: changes = recorded at path
  induction path with
  | done => contradiction
  | @same start next finish first labels effects step same _ ih =>
    obtain ⟨leading, label, trailing, before, after, rfl, front, write, delta, different, tail⟩ := ih effectList
    exact ⟨first :: leading, label, trailing, before, after, rfl, .same step same front, write, delta, different, tail⟩
  | @changed start next finish label labels effects step different tail _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj effectList
    exact ⟨[], label, labels, start, next, rfl, .done start, step, rfl, different, tail⟩

theorem classify (change : WriterChange sig) :
    (∃ update, change.IsSpend update) ∨ (∃ tree, change.IsRegistration tree) ∨
      ((∀ update, ¬ change.IsSpend update) ∧ (∀ tree, ¬ change.IsRegistration tree)) := by
  classical
  by_cases spends : ∃ update, change.IsSpend update
  · exact .inl spends
  by_cases registers : ∃ tree, change.IsRegistration tree
  · exact .inr (.inl registers)
  exact .inr (.inr ⟨fun _ found => spends ⟨_, found⟩, fun _ found => registers ⟨_, found⟩⟩)

open Stored.OwnedMemory.Claims in
theorem liveOfChangedSpend (state : State sig) (update : Spend) (changed : update.apply state ≠ state) : update.Live state := by
  classical
  by_contra absent
  apply changed
  cases update with
  | owner id =>
    have keeps : state.held.filter (fun entry => receiptId entry != id) = state.held := List.filter_eq_self.mpr (by
      intro entry member
      have different : receiptId entry ≠ id := fun same => absent (same ▸ List.mem_map_of_mem member)
      simp [different])
    simp [Spend.apply, keeps]
  | endpoint id =>
    have keeps : state.endpoints.filter (· != id) = state.endpoints := List.filter_eq_self.mpr (by
      intro endpoint member
      have different : endpoint ≠ id := fun same => absent (same ▸ member)
      simp [different])
    simp [Spend.apply, keeps]

variable {base : HostImpl (core3 grow) (HostState sig)} {bindings : List (Binding sig)}
variable {marks : List (Option ReturnFrame.Occurrence.Location)}

theorem ofRuns (leftRun : Steps profile ready (specDispatch ready base) start checked left)
    (rightRun : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right) :
    PairedWriterPaths profile ready base bindings start incoming checked canonical left right := by
  obtain ⟨leftEffects, leftPath⟩ := ofSteps leftRun
  obtain ⟨rightEffects, rightPath⟩ := ofSteps rightRun
  exact ⟨leftEffects, rightEffects, leftPath, rightPath⟩

theorem ofTransport (paths : OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks) :
    PairedWriterPaths profile ready base bindings start incoming checked canonical left right := by
  obtain ⟨_, tracks, _⟩ := paths
  exact ofRuns (tracks none).1.steps (tracks none).2.steps

theorem empty : VisitorWriterPath profile ready base bindings start incoming [] [] start incoming :=
  .framed (.done _) (.done _)

theorem frameNil (run : Steps profile ready dispatch start [] finish) : WriterPath profile ready dispatch start [] finish [] := by
  cases run
  exact .done _

theorem frameSingle {label}
    (run : Steps profile ready dispatch start [label] finish) (host : finish.host = start.host) :
    WriterPath profile ready dispatch start [label] finish [] := by
  cases run with
  | cons step rest => cases rest; exact .same step (congrArg HostState.writer host) (.done _)

theorem ofHostFrames (path : Plain.HostFramedSteps HostState.writer profile ready dispatch start labels finish) :
    WriterPath profile ready dispatch start labels finish [] := by
  induction path with
  | done => exact .done _
  | next step frame _ ih => exact .same step frame ih

theorem frameRead (read : PayloadPrefix.SilentLocalStep profile ready dispatch start finish) :
    WriterPath profile ready dispatch start [.tau] finish [] := by
  exact frameSingle (ReturnFrame.Occurrence.prefix_survives (read.tracks (.active 0 0))).1 read.host

theorem frameReads (run : PayloadPrefix.SilentLocalPath profile ready dispatch start labels finish) :
    WriterPath profile ready dispatch start labels finish [] := by
  induction run with
  | done => exact .done _
  | read step _ ih => exact append (frameRead step) ih

theorem frameLocal (path : PayloadPrefix.PairedLocalPath profile ready (specDispatch ready base)
    (specDispatch ready (LiveDispatch.host bindings base)) start incoming checked canonical left right) :
    WriterPath profile ready (specDispatch ready base) start checked left [] ∧
    WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right [] := by
  induction path with
  | done => exact ⟨.done _, .done _⟩
  | checkedRead read _ ih => exact ⟨append (frameRead read) ih.1, ih.2⟩
  | canonicalRead read _ ih => exact ⟨ih.1, append (frameRead read) ih.2⟩
  | step _ left right leftHost rightHost _ _ ih =>
    exact ⟨.same left (congrArg HostState.writer leftHost) ih.1, .same right (congrArg HostState.writer rightHost) ih.2⟩

theorem frameLeaf (path : PairedLeafSteps profile ready (specDispatch ready base)
    (specDispatch ready (LiveDispatch.host bindings base)) start incoming checked left right) :
    WriterPath profile ready (specDispatch ready base) start checked left [] ∧
    WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming checked right [] := by
  induction path with
  | done => exact ⟨.done _, .done _⟩
  | step _ left right leftHost rightHost _ _ _ ih =>
    exact ⟨.same left (congrArg HostState.writer leftHost) ih.1, .same right (congrArg HostState.writer rightHost) ih.2⟩

theorem appendPaired (first : PairedWriterPaths profile ready base bindings start incoming leading canonLeading middle peer)
    (tail : PairedWriterPaths profile ready base bindings middle peer trailing canonTrailing finish target) :
    PairedWriterPaths profile ready base bindings start incoming (leading ++ trailing) (canonLeading ++ canonTrailing) finish target := by
  obtain ⟨_, _, lhs, rhs⟩ := first
  obtain ⟨_, _, leftTail, rightTail⟩ := tail
  exact ⟨_, _, append lhs leftTail, append rhs rightTail⟩

theorem framedDiscrepancies {pending : Stored.OwnedMemory.Claims.Spend → Prop}
    (checkedPath : WriterPath profile ready (specDispatch ready base) start checked left [])
    (canonicalPath : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right [])
    (related : start.host.writer.ClaimDiscrepancies incoming.host.writer pending) :
    left.host.writer.ClaimDiscrepancies right.host.writer pending := by
  simpa only [spend checkedPath (updates := []) .nil, spend canonicalPath (updates := []) .nil, List.foldl_nil] using related

theorem publicationDiscrepancies {tree : Stored.OwnedMemory.Tree sig} {pending : Stored.OwnedMemory.Claims.Spend → Prop}
    (paths : PairedPublicationWriterPrefix profile ready base bindings tree start incoming checked left right)
    (related : start.host.writer.ClaimDiscrepancies incoming.host.writer pending) :
    left.host.writer.ClaimDiscrepancies right.host.writer pending := by
  by_cases early : checked.length < 2
  · simp [PairedPublicationWriterPrefix, ComponentPublicationWriterPrefix, early] at paths
    exact framedDiscrepancies paths.1 paths.2 related
  · simp [PairedPublicationWriterPrefix, ComponentPublicationWriterPrefix, early] at paths
    exact related.register paths.1.2.1 paths.2.2.1

open Stored.OwnedMemory.Claims in
private theorem endpointSpendWriter {site : SharedEndpointGive} {ticket : Nat}
    (executed : ExecutedSharedEndpointSpend profile ready dispatch site ticket start finish) :
    finish.host.writer = (Spend.endpoint site.identity).apply start.host.writer ∧
    WriterPath profile ready dispatch start [.tau, .tau, .tau, .tau] finish [(start.host.writer, finish.host.writer)] := by
  obtain ⟨cursor, guarded, prepared, writing, _, live, _, rfl, rfl, rfl, rfl, first, second, read, commit⟩ := executed.executed
  refine ⟨rfl, .same first rfl (.same second rfl (.same read rfl (.changed commit ?_ (.done _))))⟩
  intro unchanged
  apply Spend.not_live (.endpoint site.identity) start.host.writer
  change (Spend.endpoint site.identity).apply start.host.writer = start.host.writer at unchanged
  rw [unchanged]
  exact live

theorem ofVisitor (path : VisitorWriterPath profile ready base bindings start incoming checked canonical left right) :
    PairedWriterPaths profile ready base bindings start incoming checked canonical left right := by
  induction path with
  | framed lhs rhs => exact ⟨[], [], lhs, rhs⟩
  | prepare _ lhs rhs => exact ⟨[], [], lhs, rhs⟩
  | registrationMismatch _ lhs rhs => exact ⟨[], [], lhs, rhs⟩
  | sharedGiveMismatch _ lhs rhs => exact ⟨[], [], lhs, rhs⟩
  | endpointCommit lhs rhs => exact ⟨_, _, (endpointSpendWriter lhs).2, (endpointSpendWriter rhs).2⟩
  | guarded paths =>
    obtain ⟨_, changes, lhs, rhs, _⟩ := paths
    exact ⟨changes, [], lhs, rhs⟩
  | @publication start incoming labels left right tree paths =>
    by_cases early : labels.length < 2
    · simp [PairedPublicationWriterPrefix, ComponentPublicationWriterPrefix, early] at paths
      exact ⟨[], [], paths.1, paths.2⟩
    · simp [PairedPublicationWriterPrefix, ComponentPublicationWriterPrefix, early] at paths
      exact ⟨_, _, paths.1.1, paths.2.1⟩
  | callbackBoundary _ paths => exact paths
  | append _ _ leading trailing => exact appendPaired leading trailing

theorem checkedSpends (leftPath : WriterPath profile ready (specDispatch ready base) start checked left changes)
    (rightPath : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right [])
    (spends : List.Forall₂ WriterChange.IsSpend changes updates) :
    CheckedSpendFlow start.host.writer incoming.host.writer left.host.writer right.host.writer updates :=
  ⟨spend leftPath spends, spend rightPath (updates := []) .nil⟩

open Stored.OwnedMemory.Claims in
theorem registrationProbe_observations {left right : State sig}
    {tree : Stored.OwnedMemory.Tree sig} (checks : left.RegistrationChecksAgree right tree)
    (length : left.accepted.length = right.accepted.length) :
    componentRegistration left tree = componentRegistration right tree := by
  have observed := register_observations checks length
  cases lhs : left.register tree <;> cases rhs : right.register tree <;>
    simp_all only [Except.map, Except.error.injEq, Except.ok.injEq, reduceCtorEq, componentRegistration]

private theorem writerSteps (writer : WriterPath profile ready dispatch start labels finish changes) :
    Steps profile ready dispatch start labels finish := by
  induction writer with
  | done => exact .refl _
  | same step _ _ next | changed step _ _ next => exact .cons step next

private theorem singleWriterStep {label}
    (writer : WriterPath profile ready dispatch start [label] finish changes) :
    Step profile ready dispatch start label finish := by
  cases writerSteps writer with
  | cons step rest => cases rest; exact step

open ReturnFrame.Occurrence in
private theorem stationaryReadTrail {reader after : Config (core3 grow) (HostState sig)}
    (read : Step profile ready dispatch reader .tau after) (edit : transitionEdit reader .tau = .same)
    (place : Option Location) :
    Trail profile ready dispatch reader place [.tau] after place := by
  apply Trail.step read
  have kept : place.bind (transitionEdit reader .tau).follow = place := by
    rw [edit]
    cases place <;> rfl
  rw [kept]
  exact .done _ _

open ReturnFrame.Occurrence in
private theorem prepareReadOccurrences {atLeft atRight reader : Config (core3 grow) (HostState sig)}
    {localChecked localRaw : Trace grow sig} {plan}
    (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
    (site : ExecutedPrepareRead profile ready base atLeft reader left right localChecked plan)
    (raw : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) atRight localRaw right []) :
    ReachedReadOccurrences profile ready (specDispatch ready base) start reader left (checked ++ localChecked) ∧
    (∀ place, ∃ reached, Trail profile ready (specDispatch ready (LiveDispatch.host bindings base))
      incoming place (canonical ++ localRaw) right reached) := by
  obtain ⟨_, _, check, canon⟩ := ofVisitor front
  obtain ⟨cursor, _, focus⟩ := site.focus
  have edit : transitionEdit reader .tau = .same := by
    rw [transitionEdit, focus]
    rfl
  constructor
  · intro place
    obtain ⟨middle, first⟩ := Trail.follow_steps (writerSteps check) place
    obtain ⟨reached, through⟩ := Trail.follow_steps site.beforeRead middle
    exact ⟨reached, first.append through, stationaryReadTrail site.read edit reached⟩
  · intro place
    obtain ⟨middle, first⟩ := Trail.follow_steps (writerSteps canon) place
    obtain ⟨reached, through⟩ := Trail.follow_steps (writerSteps raw) middle
    exact ⟨reached, first.append through⟩

open ReturnFrame.Occurrence in
private theorem registrationReadOccurrences {atLeft atRight : Config (core3 grow) (HostState sig)}
    {check canon leftTicket rightTicket caller tree}
    (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
    (site : RegistrationProbeMismatch atLeft atRight left right check canon leftTicket rightTicket caller tree)
    (lhs : WriterPath profile ready (specDispatch ready base) atLeft [.tau] left [])
    (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) atRight [.tau] right []) :
    ReachedReadOccurrences profile ready (specDispatch ready base) start atLeft left checked ∧
    ReachedReadOccurrences profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming atRight right canonical := by
  obtain ⟨_, _, checked, canonical⟩ := ofVisitor front
  constructor
  · intro place
    obtain ⟨reached, leading⟩ := Trail.follow_steps (writerSteps checked) place
    exact ⟨reached, leading, stationaryReadTrail (singleWriterStep lhs) (by rw [transitionEdit, site.leftFocus]; cases caller <;> rfl) reached⟩
  · intro place
    obtain ⟨reached, leading⟩ := Trail.follow_steps (writerSteps canonical) place
    exact ⟨reached, leading, stationaryReadTrail (singleWriterStep rhs) (by rw [transitionEdit, site.rightFocus]; cases caller <;> rfl) reached⟩

open Stored.OwnedMemory.Claims in
private theorem sharedGiveObservation (claim : SharedGiveClaim) {lhs rhs : State sig}
    (agrees : claim.demand.ObservationAgrees lhs rhs) :
    claim.observe lhs = claim.observe rhs := by
  cases claim with
  | giveOwner resource id | dropOwner resource id =>
    exact State.prepare_observation_eq resource id agrees
  | endpoint _ _ id =>
    change (id ∈ lhs.endpoints ↔ id ∈ rhs.endpoints) at agrees
    simp only [SharedGiveClaim.observe, State.spendEndpoint]
    by_cases live : id ∈ lhs.endpoints
    · simp only [live, agrees.mp live, ite_true, Except.map]
    · have absent : id ∉ rhs.endpoints := fun found => live (agrees.mpr found)
      simp only [live, absent, ite_false]

open ReturnFrame.Occurrence in
private theorem sharedGiveReadOccurrences {atLeft atRight : Config (core3 grow) (HostState sig)}
    {check canon leftTicket rightTicket inst claim}
    (front : VisitorWriterPath profile ready base bindings start incoming checked canonical atLeft atRight)
    (site : SharedGiveProbeMismatch claim inst leftTicket rightTicket atLeft atRight left right check canon)
    (lhs : WriterPath profile ready (specDispatch ready base) atLeft [.tau] left [])
    (rhs : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) atRight [.tau] right []) :
    ReachedReadOccurrences profile ready (specDispatch ready base) start atLeft left checked ∧
    ReachedReadOccurrences profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming atRight right canonical := by
  obtain ⟨_, _, checked, canonical⟩ := ofVisitor front
  constructor
  · intro place
    obtain ⟨reached, leading⟩ := Trail.follow_steps (writerSteps checked) place
    exact ⟨reached, leading, stationaryReadTrail (singleWriterStep lhs) (by rw [transitionEdit, site.leftFocus]; rfl) reached⟩
  · intro place
    obtain ⟨reached, leading⟩ := Trail.follow_steps (writerSteps canonical) place
    exact ⟨reached, leading, stationaryReadTrail (singleWriterStep rhs) (by rw [transitionEdit, site.rightFocus]; rfl) reached⟩

open Stored.OwnedMemory.Claims Stored.OwnedMemory.Claims.Record in
theorem discrepancyCut (path : VisitorWriterPath profile ready base bindings start incoming checked canonical left right)
    {pending : Stored.OwnedMemory.Claims.Spend → Prop}
    (initial : start.host.writer.ClaimDiscrepancies incoming.host.writer pending) :
    WriterDiscrepancyCut profile ready base bindings start incoming pending checked canonical left right := by
  have noSteps {lhs rhs : Config (core3 grow) (HostState sig)} :
      ClassifiedWriterPrefix profile ready base bindings lhs rhs [] [] lhs rhs [] := .framed (.done _) (.done _)
  induction path generalizing pending with
  | framed checked canonical =>
    exact .complete [] (.framed checked canonical)
      (by simpa only [List.not_mem_nil, or_false] using framedDiscrepancies checked canonical initial)
  | @prepare start incoming reader leading rawLeading readLeft readRight plan site lhs rhs =>
    by_cases same : prepare reader.store reader.host.writer plan = prepare reader.store readRight.host.writer plan
    · exact .complete [] (.framed lhs rhs)
        (by simpa only [List.not_mem_nil, or_false] using framedDiscrepancies lhs rhs initial)
    · have rawWriter : readRight.host.writer = incoming.host.writer := spend rhs (updates := []) .nil
      have live : reader.host.writer.ClaimDiscrepancies readRight.host.writer pending := by rwa [site.writer, rawWriter]
      obtain ⟨probe, demanded, conflict⟩ := prepare_conflict reader.store plan live same
      obtain ⟨checkedRead, rawTrail⟩ := prepareReadOccurrences (empty (start := start) (incoming := incoming)) site rhs
      simpa only [List.nil_append, List.append_nil] using
        (WriterDiscrepancyCut.prepareConflict [] (empty (start := start) (incoming := incoming)) noSteps
          (by simpa only [List.not_mem_nil, or_false] using initial) site lhs rhs checkedRead rawTrail (.inl demanded) same conflict empty)
  | @registrationMismatch start incoming readLeft readRight check canon leftTicket rightTicket caller tree site lhs rhs =>
    have live (demand : Spend) : (pending demand ∨ demand ∈ []) = pending demand := by simp
    have related := framedDiscrepancies lhs rhs initial
    have conflict : RegistrationConflict readLeft.host.writer readRight.host.writer tree pending :=
      related.registrationConflict (fun checks => site.different
        (registrationProbe_observations checks (congrArg List.length related.accepted)))
    obtain ⟨checkedRead, rawRead⟩ := registrationReadOccurrences (empty (start := start) (incoming := incoming)) site lhs rhs
    simpa only [List.nil_append, List.append_nil] using
      (WriterDiscrepancyCut.registrationConflict [] (empty (start := start) (incoming := incoming)) noSteps site lhs rhs
        checkedRead rawRead (by simpa only [live] using related) (by simpa only [live] using conflict) empty)
  | @sharedGiveMismatch start incoming readLeft readRight check canon leftTicket rightTicket inst claim site lhs rhs =>
    have related := framedDiscrepancies lhs rhs initial
    have conflict : ¬ claim.demand.ObservationAgrees readLeft.host.writer readRight.host.writer :=
      fun observes => site.different (sharedGiveObservation claim observes)
    have exceptional : pending claim.demand := Classical.byContradiction fun outside => conflict (related.observe _ outside)
    obtain ⟨checkedRead, rawRead⟩ := sharedGiveReadOccurrences (empty (start := start) (incoming := incoming)) site lhs rhs
    simpa only [List.nil_append, List.append_nil] using
      (WriterDiscrepancyCut.sharedGiveConflict [] (empty (start := start) (incoming := incoming)) noSteps site lhs rhs
        checkedRead rawRead (by simpa only [List.not_mem_nil, or_false] using related) (.inl exceptional) conflict empty)
  | @endpointCommit start incoming left right site leftTicket rightTicket lhs rhs =>
    have after := initial.spendBoth (.endpoint site.identity)
    refine .complete [] (.endpointCommit lhs rhs) ?_
    rw [(endpointSpendWriter lhs).1, (endpointSpendWriter rhs).1]
    exact ⟨after.accepted, fun probe outside => after.observe probe (fun smaller => outside (.inl smaller.1))⟩
  | guarded paths =>
    obtain ⟨source, changes, checked, canonical, empty | ⟨change, update, single, selected, nominal⟩⟩ := paths
    · subst changes
      exact .complete [] (.framed checked canonical)
        (by simpa only [List.not_mem_nil, or_false] using framedDiscrepancies checked canonical initial)
    · subst changes
      obtain ⟨lhs, rhs⟩ := checkedSpends checked canonical (.cons nominal.live .nil)
      refine .complete [update] (.spend (selected ▸ source) nominal canonical) ?_
      rw [lhs, rhs]
      simpa only [List.foldl_cons, List.foldl_nil, List.mem_singleton] using initial.spendLeft update
  | publication paths =>
    exact .complete [] (.publication paths)
      (by simpa only [List.not_mem_nil, or_false] using publicationDiscrepancies paths initial)
  | callbackBoundary boundary paths =>
    simpa only [List.nil_append, List.append_nil] using
      (WriterDiscrepancyCut.boundary [] empty noSteps (by simpa only [List.not_mem_nil, or_false] using initial)
        boundary paths empty)
  | append front tail first later =>
    cases first initial with
    | complete spends certified reached =>
      cases later reached with
      | complete more nextCertified related =>
        exact .complete (spends ++ more) (certified.append nextCertified) (by simpa only [List.mem_append, or_assoc] using related)
      | boundary more leading nextCertified related site actual trailing =>
        simpa only [List.append_assoc] using (WriterDiscrepancyCut.boundary (spends ++ more) (front.append leading)
          (certified.append nextCertified)
          (by simpa only [List.mem_append, or_assoc] using related) site actual trailing)
      | prepareConflict more leading nextCertified related site lhs rhs _ _ live unequal conflict trailing =>
        obtain ⟨checkedRead, rawTrail⟩ := prepareReadOccurrences (front.append leading) site rhs
        simpa only [List.append_assoc] using (WriterDiscrepancyCut.prepareConflict (spends ++ more) (front.append leading)
          (certified.append nextCertified)
          (by simpa only [List.mem_append, or_assoc] using related) site lhs rhs checkedRead rawTrail
          (by simpa only [List.mem_append, or_assoc] using live) unequal conflict trailing)
      | registrationConflict more leading nextCertified site lhs rhs _ _ related conflict trailing =>
        obtain ⟨checkedRead, rawRead⟩ := registrationReadOccurrences (front.append leading) site lhs rhs
        simpa only [List.append_assoc] using (WriterDiscrepancyCut.registrationConflict (spends ++ more) (front.append leading)
          (certified.append nextCertified)
          site lhs rhs checkedRead rawRead (by simpa only [List.mem_append, or_assoc] using related)
          (by simpa only [RegistrationConflict, List.mem_append, or_assoc] using conflict) trailing)
      | sharedGiveConflict more leading nextCertified site lhs rhs _ _ related live different trailing =>
        obtain ⟨checkedRead, rawRead⟩ := sharedGiveReadOccurrences (front.append leading) site lhs rhs
        simpa only [List.append_assoc] using (WriterDiscrepancyCut.sharedGiveConflict (spends ++ more) (front.append leading)
          (certified.append nextCertified)
          site lhs rhs checkedRead rawRead (by simpa only [List.mem_append, or_assoc] using related)
          (by simpa only [List.mem_append, or_assoc] using live) different trailing)
    | boundary spends leading certified related site actual trailing =>
      simpa only [List.append_assoc] using
        (WriterDiscrepancyCut.boundary spends leading certified related site actual (trailing.append tail))
    | prepareConflict spends leading certified related site lhs rhs checkedRead rawTrail live unequal conflict trailing =>
      simpa only [List.append_assoc] using
        (WriterDiscrepancyCut.prepareConflict spends leading certified related site lhs rhs checkedRead rawTrail live unequal conflict
          (trailing.append tail))
    | registrationConflict spends leading certified site lhs rhs checkedRead rawRead related conflict trailing =>
      simpa only [List.append_assoc] using
        (WriterDiscrepancyCut.registrationConflict spends leading certified site lhs rhs checkedRead rawRead related conflict
          (trailing.append tail))
    | sharedGiveConflict spends leading certified site lhs rhs checkedRead rawRead related live different trailing =>
      simpa only [List.append_assoc] using
        (WriterDiscrepancyCut.sharedGiveConflict spends leading certified site lhs rhs checkedRead rawRead related live different
          (trailing.append tail))

theorem registration {change : WriterChange sig} {tree : Stored.OwnedMemory.Tree sig}
    (path : WriterPath profile ready dispatch start labels finish [change])
    (registers : WriterChange.IsRegistration change tree) : start.host.writer.register tree = .ok finish.host.writer := by
  obtain ⟨_, _, _, before, after, _, front, _, rfl, _, tail⟩ := firstChange path
  change before.host.writer.register tree = .ok after.host.writer at registers
  have startWriter : before.host.writer = start.host.writer := spend front (updates := []) .nil
  have finalWriter : finish.host.writer = after.host.writer := spend tail (updates := []) .nil
  rw [startWriter, ← finalWriter] at registers
  exact registers

theorem visitor {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    {valueType : Type} {pending : Config (core3 grow) (HostState sig) → Prop}
    {checkNext : Except Stored.Endpoints.RecordLower.Issue valueType → Session grow sig (Ret (core3 grow))}
    {canonNext : valueType → Session grow sig (Ret (core3 grow))}
    (body : ValueVisitRun profile ready base bindings older origin valueType pending checkNext canonNext start incoming actual finish) :
    ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
      PayloadPrefix.visible checked = PayloadPrefix.visible canonical ∧ left.store = right.store ∧
      OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧
      PairedWriterPaths profile ready base bindings start incoming checked canonical left right ∧
      Steps profile ready (specDispatch ready base) left trailing finish ∧
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish marks := by
  obtain ⟨checked, canonical, trailing, left, right, marks, split, visible, stores, tracks, tail, writer, ending⟩ := body
  exact ⟨checked, canonical, trailing, left, right, marks, split, visible, stores, tracks, ofVisitor writer, tail, ending⟩

theorem stringSlice {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {description}
    (body : StringRunSlice profile ready base bindings older description start incoming actual finish) :
    ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
      PayloadPrefix.visible canonical = PayloadPrefix.visible checked ∧
      OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧
      PairedWriterPaths profile ready base bindings start incoming checked canonical left right ∧
      left.store = right.store ∧ Steps profile ready (specDispatch ready base) left trailing finish ∧
      StringSliceEnd profile ready base bindings older description left right trailing finish marks := by
  obtain ⟨checked, canonical, trailing, left, right, marks, split, visible, tracks, stores, tail, ending⟩ := body
  exact ⟨checked, canonical, trailing, left, right, marks, split, visible, tracks, ofTransport tracks, stores, tail, ending⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.WriterPaths
