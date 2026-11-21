module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch LinkedCallback.MemorySequence ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {base : HostImpl (core3 grow) (HostState sig)} {bindings : List (Binding sig)}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
  {start incoming : Config (core3 grow) (HostState sig)} {seen : Trace grow sig} {offset : Nat}
  {sink : RefusalSink grow sig}

private theorem rangePathsFrom {destination : RecordDestination} {area : Layout} {entries : List Field} {pointer : Nat}
    {left right checked canonical : Config (core3 grow) (HostState sig)} {suffix : Trace grow sig}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {refuse children wrap}
    (covers : sink.Covers profile ready base bindings start incoming offset) (admitted : sink.admits refuse)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : CollectionRangePaths profile ready base bindings left right suffix 0 destination area entries pointer checked canonical
      check refuse wrap children) :
    CollectionRangePaths profile ready base bindings start incoming (seen ++ suffix) offset destination area entries pointer
      checked canonical check refuse wrap children sink := by
  obtain ⟨bytes, sized, outcome⟩ := run
  refine ⟨bytes, sized, ?_⟩
  have trap (reason : TrapReason)
      (stopped : ComparedPaths profile ready base bindings left right (suffix ++ [.trap reason])
        (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical)) :
      ComparedPaths profile ready base bindings start incoming ((seen ++ suffix) ++ [.trap reason])
        (StepDefs.trapCfg checked) (StepDefs.trapCfg canonical) := by
    rw [List.append_assoc]
    exact CallbackPrefix.appendComparedPaths leading stopped
  by_cases aligned : pointer = alignTo pointer area.alignment
  · simp only [ite_eq_right (not_not_intro aligned)] at outcome ⊢
    by_cases bounds : pointer + entries.length * area.size ≤ bytes
    · simp only [ite_eq_left bounds] at outcome ⊢
      intro issue refused
      obtain ⟨peer, same, stopped, _⟩ := outcome issue refused
      have reached := CallbackPrefix.appendComparedSlots leading stopped
      exact ⟨peer, same, reached, covers refuse admitted (wrap issue) _ _ _ check rfl same reached⟩
    · simp only [ite_eq_right bounds] at outcome ⊢
      exact trap .outOfBounds outcome
  · simp only [ite_eq_left aligned] at outcome ⊢
    exact trap .unalignedPointer outcome

theorem allocationPaths {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {visit : Nat → Nat → Finish grow sig} {path : Nat → Nat → TrailFinish grow sig}
    (covers : sink.Covers profile ready base bindings start incoming offset)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : LiveCollectionPaths profile ready base bindings older destination inst type element entries index output checkNext canonNext
      left right check canon (fun pointer bytes _ => visit pointer bytes))
    (next : ∀ pointer bytes observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      visit pointer bytes lhs rhs cursor peer → path pointer bytes observed lhs rhs cursor peer) :
    LiveCollectionPaths profile ready base bindings older destination inst type element entries index output checkNext canonNext
      left right check canon path start incoming seen offset sink := by
  intro suffix finish steps
  obtain ⟨lhs, rhs, reached, mark, marked, paired, compared, returns⟩ := run steps
  refine ⟨lhs, rhs, reached, mark, marked, paired, CallbackPrefix.appendAllocatorPaths leading compared, ?_⟩
  intro pointer cursor top returning
  obtain ⟨range, failed, children⟩ := returns pointer cursor top returning
  refine ⟨range, rangePathsFrom covers admitted leading failed, ?_⟩
  intro bytes sized aligned bounds fresh
  obtain ⟨lhs, rhs, peer, tracks, frame, width, size, align, bound, growth, checkAt, canonAt, body⟩ :=
    children bytes sized aligned bounds fresh
  have reached := CallbackPrefix.appendComparedSlots leading tracks
  exact ⟨lhs, rhs, peer, reached, frame, width, size, align, bound, growth, checkAt, canonAt,
    next pointer bytes (seen ++ suffix) lhs rhs cursor peer reached frame.store body⟩

theorem collectionEntryPaths {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {visit : Nat → Nat → Finish grow sig} {path : Nat → Nat → TrailFinish grow sig}
    (covers : sink.Covers profile ready base bindings start incoming offset)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      left right check canon (fun pointer bytes _ => visit pointer bytes))
    (next : ∀ pointer bytes observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      visit pointer bytes lhs rhs cursor peer → path pointer bytes observed lhs rhs cursor peer) :
    LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      left right check canon path start incoming seen offset sink := by
  unfold LiveCollectionEntry at run ⊢
  cases prepared : Stored.OwnedMemory.Claims.Record.prepare left.store left.host.writer (Field.listObjects entries) with
  | error issue =>
    simp only [prepared] at run ⊢
    have reached := CallbackPrefix.appendComparedSlots leading run.2.2.1
    rw [List.append_nil] at reached
    exact ⟨run.1, run.2.1, reached, covers _ admitted _ _ _ _ check rfl run.1 reached⟩
  | ok value =>
    cases value
    simp only [prepared] at run ⊢
    exact fun width => allocationPaths covers admitted leading (run width) next

theorem descriptorPaths {output : Stored.Lower.Output} {checkNext : ValueCheckNext grow sig output}
    {canonNext : ValueCanonNext grow sig output} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {finish : ValueFinish grow sig output} {visit : TrailFinish grow sig}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : LiveListPublish profile ready base bindings output checkNext canonNext finish left right check canon)
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalPathsThen profile ready base bindings start incoming seen offset visit := by
  obtain ⟨store, result, labels, shape, lhs, rhs, continued⟩ := run
  cases result with
  | error reason =>
    have trapped : PayloadPrefix.visible labels = [.trap reason] := CallbackPrefix.visibleLeaf shape
    exact .inl ⟨reason, [], _, _, CallbackPrefix.appendComparedPaths leading
      ⟨labels, labels, lhs.steps, rhs.steps, trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok value =>
    obtain ⟨leftTracks, rightTracks, finished⟩ := continued value rfl
    have reached := CallbackPrefix.appendComparedSlots leading
      ⟨labels, labels, leftTracks, rightTracks, rfl, rfl⟩
    exact .inr ⟨PayloadPrefix.visible labels, _, _, check, canon, reached, rfl, next value _ _ _ _ _ reached rfl finished⟩

private theorem canonicalRead {left right reached : Config (core3 grow) (HostState sig)} {labels : Trace grow sig}
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : ReturnFrame.Occurrence.RetainsActiveSlots profile ready (specDispatch ready (LiveDispatch.host bindings base))
      right labels reached)
    (quiet : PayloadPrefix.visible labels = []) :
    ComparedSlots profile ready base bindings start incoming seen left reached offset := by
  simpa only [List.append_nil] using CallbackPrefix.appendComparedSlots (after := []) leading
    ⟨[], labels, (fun _ => .done _ _), run, rfl, quiet⟩

theorem mapEntryPaths {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType}
    {element : Stored.TypeOf} {output : Stored.Lower.Output} {field value : Field} {index pointer : Nat}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldPaths profile ready base bindings start incoming offset child paths sink)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (run : liveCollectionMapEntry profile ready base bindings older destination inst key element output field value index pointer
      child checkNext canonNext finish left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveMapEntryPaths profile ready base bindings older destination inst key element output start incoming offset paths
      field value index pointer checkNext canonNext visit seen left right check canon := by
  unfold liveCollectionMapEntry at run
  unfold liveMapEntryPaths
  split at run
  · rename_i stringKey
    subst key
    simp only [↓reduceIte]
    exact CallbackPrefix.stringMapEntryPaths leading run
      (fun address observed lhs rhs cursor peer tracks same body =>
        lift value 1 address lhs rhs cursor peer _ canonNext finish visit observed body tracks same (sink.nested _ admitted index) next)
  · rename_i notString
    simp only [notString, ↓reduceIte]
    obtain ⟨keyRead, keyQuiet, keyTracks, store, result, lhsLabels, rhsLabels, lhs, rhs, same, tail⟩ := run
    have atKey := canonicalRead leading keyTracks keyQuiet
    cases result with
    | error reason =>
      obtain ⟨before, trapped⟩ := tail
      exact .inl ⟨reason, before, _, _, CallbackPrefix.appendComparedPaths atKey
        ⟨lhsLabels, rhsLabels, lhs, rhs.steps, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
    | ok done =>
      cases done
      obtain ⟨lhsTracks, rhsTracks, valueRead, valueQuiet, valueTracks, body⟩ := tail
      have atValue := canonicalRead (CallbackPrefix.appendComparedSlots atKey
        ⟨lhsLabels, rhsLabels, lhsTracks, rhsTracks, rfl, same.symm⟩) valueTracks valueQuiet
      exact .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, atValue, rfl,
        lift value 1 _ _ _ check canon _ canonNext finish visit _ body atValue rfl (sink.nested _ admitted index) next⟩

theorem mapElementsPaths {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType}
    {element : Stored.TypeOf} {output : Stored.Lower.Output} {entries : List Field} {index pointer : Nat}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldPaths profile ready base bindings start incoming offset child paths sink)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (same : left.store = right.store)
    (run : liveMapElementsWith (liveCollectionMapEntry profile ready base bindings older destination inst key element output)
      destination inst key element output child checkNext canonNext finish entries index pointer left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveMapElementsPaths (liveMapEntryPaths profile ready base bindings older destination inst key element output start incoming offset paths)
      destination inst key element output checkNext canonNext visit entries index pointer seen left right check canon := by
  induction entries generalizing index pointer seen left right check canon with
  | nil => exact next seen left right check canon leading same run
  | cons item rest ih =>
    obtain ⟨payload, value, shape, entry⟩ := run
    exact ⟨payload, value, shape, mapEntryPaths lift leading entry admitted
      (fun _ _ _ _ _ tracks shared tail => ih tracks shared tail)⟩

theorem fixedPaths {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {entries : List Field} {index address : Nat} {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldPaths profile ready base bindings start incoming offset child paths sink)
    (leading : ComparedSlots profile ready base bindings start incoming seen left right offset)
    (same : left.store = right.store)
    (run : LiveFixedThen profile ready base bindings destination inst child element entries index address checkNext canonNext finish
      left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedSlots profile ready base bindings start incoming observed lhs rhs offset → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveFixedPaths profile ready base bindings destination inst paths element entries index address checkNext canonNext visit
      seen left right check canon := by
  obtain ⟨read, body⟩ := run
  exact ⟨read, CallbackPrefix.liveElementsPathsFrom lift (canonicalRead leading read rfl) same body (sink.nested _ admitted index) next⟩

private theorem emptyLift :
    LiftsFieldPaths profile ready base bindings start incoming offset
      (fun _ _ _ _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ _ _ => False) sink := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ impossible
  exact impossible.elim

private theorem variantLift (destination : RecordDestination) (inst : InstId)
    (cases : List (String × Option Stored.TypeOf)) (tag : Nat)
    (arms : ∀ name type, (name, some type) ∈ cases → LiftsFieldPaths profile ready base bindings start incoming offset
      (liveCollectionField profile ready base bindings older destination inst type)
      (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type) sink) :
    LiftsFieldPaths profile ready base bindings start incoming offset
      (liveVariantArm profile ready base bindings older destination inst cases tag)
      (liveVariantPaths profile ready base bindings older destination inst start incoming offset sink cases tag) sink := by
  induction cases generalizing tag with
  | nil => cases tag <;> exact emptyLift
  | cons field rest ih =>
    obtain ⟨name, arm⟩ := field
    cases tag with
    | zero => cases arm with
      | none => exact emptyLift
      | some type => exact arms name type (List.mem_cons_self ..)
    | succ tag =>
      simpa only [liveVariantArm, liveVariantPaths] using
        (ih tag (fun name type member => arms name type (List.mem_cons_of_mem _ member)))

private theorem aggregateSelectionLift
    {fields : List (Stored.TypeOf × FieldComparison grow sig)} {paths : List (Stored.TypeOf × TrailFieldComparison grow sig)}
    (paired : ∀ type raw, (type, raw) ∈ fields → ∃ trail, (type, trail) ∈ paths ∧
      LiftsFieldPaths profile ready base bindings start incoming offset raw trail sink) :
    LiftsFieldPaths profile ready base bindings start incoming offset (aggregateChild fields) (selectPathField paths) sink := by
  intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
  obtain ⟨raw, member, body⟩ := run
  obtain ⟨trail, present, lift⟩ := paired item.type raw member
  exact ⟨trail, present, lift item index address left right check canon checkNext canonNext finish visit before body leading same admitted next⟩

private theorem tupleLift (destination : RecordDestination) (inst : InstId) (types : List Stored.TypeOf)
    (children : ∀ type ∈ types, LiftsFieldPaths profile ready base bindings start incoming offset
      (liveCollectionField profile ready base bindings older destination inst type)
      (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type) sink) :
    LiftsFieldPaths profile ready base bindings start incoming offset
      (aggregateChild (liveTupleFields profile ready base bindings older destination inst types))
      (selectPathField (liveTupleTrails profile ready base bindings older destination inst start incoming offset sink types)) sink := by
  apply aggregateSelectionLift
  intro type raw member
  induction types with
  | nil => cases member
  | cons schema rest ih =>
    rw [liveTupleFields] at member
    rcases List.mem_cons.mp member with equal | later
    · cases equal
      exact ⟨_, List.mem_cons_self .., children _ (List.mem_cons_self ..)⟩
    · obtain ⟨trail, present, lift⟩ := ih (fun item belongs => children item (List.mem_cons_of_mem _ belongs)) later
      exact ⟨trail, List.mem_cons_of_mem _ present, lift⟩

private theorem recordTrails (destination : RecordDestination) (inst : InstId) (fields : List (String × Stored.TypeOf)) :
    liveRecordTrails profile ready base bindings older destination inst start incoming offset sink fields =
      liveTupleTrails profile ready base bindings older destination inst start incoming offset sink (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    cases field
    simp only [liveRecordTrails, List.map_cons, liveTupleTrails, ih]

theorem fieldPaths {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf}
    (covers : sink.Covers profile ready base bindings start incoming offset) (family : RecursiveCollectionType type) :
    LiftsFieldPaths profile ready base bindings start incoming offset
      (liveCollectionField profile ready base bindings older destination inst type)
      (liveRecursivePaths profile ready base bindings older destination inst start incoming offset sink type) sink := by
  induction family with
  | leaf nominal =>
    have lifted := CallbackPrefix.leafFieldLift (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      (older := older) (start := start) (incoming := incoming) (offset := offset) (destination := destination) (inst := inst) covers (.inl nominal)
    cases nominal <;> exact lifted
  | data data =>
    have lifted := CallbackPrefix.leafFieldLift (profile := profile) (ready := ready) (base := base) (bindings := bindings)
      (older := older) (start := start) (incoming := incoming) (offset := offset) (destination := destination) (inst := inst) covers (.inr (.inl data))
    cases data with
    | @primitive primitive notString => cases primitive <;> exact lifted
    | enum | flags => exact lifted
  | string => exact CallbackPrefix.leafFieldLift covers (.inr (.inr rfl))
  | list _ child =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨entries, shape, body⟩ := run
    refine ⟨entries, shape, collectionEntryPaths covers admitted leading body ?_⟩
    intro pointer bytes observed lhs rhs cursor peer reached shared elements
    exact CallbackPrefix.liveElementsPathsFrom child reached shared elements (sink.nested _ admitted index)
      (fun _ _ _ _ _ terminal _ publish => descriptorPaths terminal publish (fun value => by cases value; exact next))
  | map _ child =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨entries, shape, body⟩ := run
    refine ⟨entries, shape, collectionEntryPaths covers admitted leading body ?_⟩
    intro pointer bytes observed lhs rhs cursor peer reached shared elements
    exact mapElementsPaths child reached shared elements (sink.nested _ admitted index)
      (fun _ _ _ _ _ terminal _ publish => descriptorPaths terminal publish (fun value => by cases value; exact next))
  | fixed _ child =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨entries, shape, body⟩ := run
    exact ⟨entries, shape, fixedPaths child leading same body admitted next⟩
  | option _ child =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨tag, selected, shape, body⟩ := run
    refine ⟨tag, selected, shape, ?_⟩
    cases selected <;> exact CallbackPrefix.sumPathsFrom (fun _ => child) leading body admitted next
  | @result success failure _ _ okChild errChild =>
    cases success <;> cases failure <;>
      intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    all_goals
      obtain ⟨tag, selected, shape, body⟩ := run
      refine ⟨tag, selected, shape, ?_⟩
      by_cases ok : tag = 0 <;> simp only [ok, ↓reduceIte] at body ⊢ <;> cases selected <;> first
        | exact CallbackPrefix.sumPathsFrom (fun _ => emptyLift) leading body admitted next
        | exact CallbackPrefix.sumPathsFrom (fun _ => okChild _ rfl) leading body admitted next
        | exact CallbackPrefix.sumPathsFrom (fun _ => errChild _ rfl) leading body admitted next
  | @variant cases _ arms =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨tag, selected, shape, body⟩ := run
    refine ⟨tag, selected, shape, ?_⟩
    cases selected <;> exact CallbackPrefix.sumPathsFrom (fun _ => variantLift destination inst cases tag arms) leading body admitted next
  | @record fields _ children =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨items, shape, body⟩ := run
    have lift := tupleLift destination inst (fields.map Prod.snd) (fun type member => by
      obtain ⟨⟨name, schema⟩, present, rfl⟩ := List.mem_map.mp member
      exact children name schema present)
    rw [← CallbackPrefix.recordTable destination inst, ← recordTrails destination inst] at lift
    exact ⟨items, shape, CallbackPrefix.aggregatePathsFrom lift leading same body admitted next⟩
  | @tuple types _ children =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨items, shape, body⟩ := run
    exact ⟨items, shape, CallbackPrefix.aggregatePathsFrom (tupleLift destination inst types children) leading same body admitted next⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails
