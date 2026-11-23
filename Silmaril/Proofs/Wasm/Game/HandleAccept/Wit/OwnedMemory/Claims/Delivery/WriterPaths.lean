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

open Stored.OwnedMemory.Claims in
theorem spendStep {label : Label (core3 grow) (HostState sig)} (update : Spend)
    (step : Step profile ready dispatch start label finish)
    (assigned : finish.host.writer = update.apply start.host.writer) :
    ∃ changes, WriterPath profile ready dispatch start [label] finish changes ∧
      (changes = [] ∨ ∃ change nominal, changes = [change] ∧ some update = some nominal ∧ change.IsSpend nominal) := by
  classical
  by_cases same : finish.host.writer = start.host.writer
  · exact ⟨[], .same step same (.done _), .inl rfl⟩
  · exact ⟨_, .changed step same (.done _), .inr ⟨_, update, rfl, rfl,
      liveOfChangedSpend _ update (assigned ▸ same), assigned⟩⟩

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
    exact related.register paths.1.2 paths.2.2

theorem ofVisitor (path : VisitorWriterPath profile ready base bindings start incoming checked canonical left right) :
    PairedWriterPaths profile ready base bindings start incoming checked canonical left right := by
  induction path with
  | framed lhs rhs => exact ⟨[], [], lhs, rhs⟩
  | prepare _ lhs rhs => exact ⟨[], [], lhs, rhs⟩
  | registrationMismatch _ lhs rhs => exact ⟨[], [], lhs, rhs⟩
  | guarded paths =>
    obtain ⟨changes, lhs, rhs, _⟩ := paths
    exact ⟨changes, [], lhs, rhs⟩
  | @publication start incoming labels left right tree paths =>
    by_cases early : labels.length < 2
    · simp [PairedPublicationWriterPrefix, ComponentPublicationWriterPrefix, early] at paths
      exact ⟨[], [], paths.1, paths.2⟩
    · simp [PairedPublicationWriterPrefix, ComponentPublicationWriterPrefix, early] at paths
      exact ⟨_, _, paths.1.1, paths.2.1⟩
  | allocation _ paths => exact paths
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

open Stored.OwnedMemory.Claims Stored.OwnedMemory.Claims.Record in
theorem discrepancyCut (path : VisitorWriterPath profile ready base bindings start incoming checked canonical left right)
    {pending : Stored.OwnedMemory.Claims.Spend → Prop}
    (initial : start.host.writer.ClaimDiscrepancies incoming.host.writer pending) :
    WriterDiscrepancyCut profile ready base bindings start incoming pending checked canonical left right := by
  induction path generalizing pending with
  | framed checked canonical =>
    exact .complete [] (by simpa only [List.not_mem_nil, or_false] using framedDiscrepancies checked canonical initial)
  | @prepare start incoming reader leading rawLeading readLeft readRight plan site lhs rhs =>
    by_cases same : prepare reader.store reader.host.writer plan = prepare reader.store readRight.host.writer plan
    · exact .complete [] (by simpa only [List.not_mem_nil, or_false] using framedDiscrepancies lhs rhs initial)
    · have rawWriter : readRight.host.writer = incoming.host.writer := spend rhs (updates := []) .nil
      have live : reader.host.writer.ClaimDiscrepancies readRight.host.writer pending := by rwa [site.writer, rawWriter]
      obtain ⟨probe, demanded, conflict⟩ := prepare_conflict reader.store plan live same
      simpa only [List.nil_append, List.append_nil] using
        (WriterDiscrepancyCut.prepareConflict [] (empty (start := start) (incoming := incoming))
          (by simpa only [List.not_mem_nil, or_false] using initial) site lhs rhs (.inl demanded) same conflict empty)
  | @registrationMismatch start incoming readLeft readRight check canon leftTicket rightTicket caller tree site lhs rhs =>
    have live (demand : Spend) : (pending demand ∨ demand ∈ []) = pending demand := by simp
    have related := framedDiscrepancies lhs rhs initial
    have conflict : RegistrationConflict readLeft.host.writer readRight.host.writer tree pending :=
      related.registrationConflict (fun checks => site.different
        (registrationProbe_observations checks (congrArg List.length related.accepted)))
    simpa only [List.nil_append, List.append_nil] using
      (WriterDiscrepancyCut.registrationConflict [] (empty (start := start) (incoming := incoming)) site lhs rhs
        (by simpa only [live] using related) (by simpa only [live] using conflict) empty)
  | guarded paths =>
    obtain ⟨changes, checked, canonical, empty | ⟨change, update, single, _, nominal⟩⟩ := paths
    · subst changes
      exact .complete [] (by simpa only [List.not_mem_nil, or_false] using framedDiscrepancies checked canonical initial)
    · subst changes
      obtain ⟨lhs, rhs⟩ := checkedSpends checked canonical (.cons nominal .nil)
      refine .complete [update] ?_
      rw [lhs, rhs]
      simpa only [List.foldl_cons, List.foldl_nil, List.mem_singleton] using initial.spendLeft update
  | publication paths =>
    exact .complete [] (by simpa only [List.not_mem_nil, or_false] using publicationDiscrepancies paths initial)
  | allocation boundary paths =>
    simpa only [List.nil_append, List.append_nil] using
      (WriterDiscrepancyCut.boundary [] empty (by simpa only [List.not_mem_nil, or_false] using initial)
        (.inl boundary) paths empty)
  | callbackBoundary boundary paths =>
    simpa only [List.nil_append, List.append_nil] using
      (WriterDiscrepancyCut.boundary [] empty (by simpa only [List.not_mem_nil, or_false] using initial)
        (.inr boundary) paths empty)
  | append front tail first later =>
    cases first initial with
    | complete spends reached =>
      cases later reached with
      | complete more related =>
        exact .complete (spends ++ more) (by simpa only [List.mem_append, or_assoc] using related)
      | boundary more leading related site actual trailing =>
        simpa only [List.append_assoc] using (WriterDiscrepancyCut.boundary (spends ++ more) (front.append leading)
          (by simpa only [List.mem_append, or_assoc] using related) site actual trailing)
      | prepareConflict more leading related site lhs rhs live unequal conflict trailing =>
        simpa only [List.append_assoc] using (WriterDiscrepancyCut.prepareConflict (spends ++ more) (front.append leading)
          (by simpa only [List.mem_append, or_assoc] using related) site lhs rhs
          (by simpa only [List.mem_append, or_assoc] using live) unequal conflict trailing)
      | registrationConflict more leading site lhs rhs related conflict trailing =>
        simpa only [List.append_assoc] using (WriterDiscrepancyCut.registrationConflict (spends ++ more) (front.append leading)
          site lhs rhs (by simpa only [List.mem_append, or_assoc] using related)
          (by simpa only [RegistrationConflict, List.mem_append, or_assoc] using conflict) trailing)
    | boundary spends leading related site actual trailing =>
      simpa only [List.append_assoc] using
        (WriterDiscrepancyCut.boundary spends leading related site actual (trailing.append tail))
    | prepareConflict spends leading related site lhs rhs live unequal conflict trailing =>
      simpa only [List.append_assoc] using
        (WriterDiscrepancyCut.prepareConflict spends leading related site lhs rhs live unequal conflict (trailing.append tail))
    | registrationConflict spends leading site lhs rhs related conflict trailing =>
      simpa only [List.append_assoc] using
        (WriterDiscrepancyCut.registrationConflict spends leading site lhs rhs related conflict (trailing.append tail))

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
