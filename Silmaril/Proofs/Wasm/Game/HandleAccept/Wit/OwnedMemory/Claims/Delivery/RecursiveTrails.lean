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
      check refuse wrap children left right suffix) :
    CollectionRangePaths profile ready base bindings start incoming (seen ++ suffix) offset destination area entries pointer
      checked canonical check refuse wrap children left right suffix sink := by
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
      obtain ⟨peer, same, stopped, occurrences, transport, _⟩ := outcome issue refused
      have reached := CallbackPrefix.appendComparedSlots leading stopped
      exact ⟨peer, same, reached, occurrences, transport, covers refuse admitted (wrap issue) _ _ _ check rfl same reached⟩
    · simp only [ite_eq_right bounds] at outcome ⊢
      exact ⟨trap .outOfBounds outcome.1, outcome.2⟩
  · simp only [ite_eq_left aligned] at outcome ⊢
    exact ⟨trap .unalignedPointer outcome.1, outcome.2⟩

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
  refine ⟨run.1, ?_⟩
  intro pathIndex suffix finish steps
  obtain ⟨lhs, rhs, reached, mark, marked, paired, compared, occurrences, transport, exactPath, returns⟩ := run.2 steps
  refine ⟨lhs, rhs, reached, mark, marked, paired, CallbackPrefix.appendAllocatorPaths leading compared, occurrences, transport, exactPath, ?_⟩
  intro pointer cursor top returning
  obtain ⟨range, failed, children⟩ := returns pointer cursor top returning
  refine ⟨range, rangePathsFrom covers admitted leading failed, ?_⟩
  intro bytes sized aligned bounds fresh
  obtain ⟨lhs, rhs, peer, tracks, occurrences, retained, frame, width, size, align, bound, growth, checkAt, canonAt, body⟩ :=
    children bytes sized aligned bounds fresh
  have reached := CallbackPrefix.appendComparedSlots leading tracks
  exact ⟨lhs, rhs, peer, reached, occurrences, retained, frame, width, size, align, bound, growth, checkAt, canonAt,
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
    exact ⟨run.1, run.2.1, reached, run.2.2.2.1, run.2.2.2.2.1, covers _ admitted _ _ _ _ check rfl run.1 reached⟩
  | ok value =>
    cases value
    simp only [prepared] at run ⊢
    exact fun width => allocationPaths covers admitted leading (run width) next

theorem collectionEntryOccurrencesWith {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {visit : Nat → Nat → Finish grow sig} {path : Nat → Nat → TrailFinish grow sig}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      left right check canon (fun pointer bytes _ => visit pointer bytes))
    (next : ∀ pointer bytes suffix lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming (seen ++ suffix) lhs rhs →
      ComparedOccurrenceTransport profile ready base bindings left right suffix lhs rhs →
      visit pointer bytes lhs rhs cursor peer → path pointer bytes (seen ++ suffix) lhs rhs cursor peer) :
    LiveCollectionOccurrenceEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming left right seen check canon path sink := by
  unfold LiveCollectionEntry at run
  unfold LiveCollectionOccurrenceEntry
  cases prepared : Stored.OwnedMemory.Claims.Record.prepare left.store left.host.writer (Field.listObjects entries) with
  | error issue =>
    simp only [prepared] at run ⊢
    have reached := CallbackPrefix.appendComparedOccurrences leading run.2.2.2.1
    rw [List.append_nil] at reached
    exact ⟨reached, run.2.2.2.2.1, covers _ admitted _ _ _ _ check rfl reached⟩
  | ok value =>
    cases value
    simp only [prepared] at run ⊢
    intro width
    refine ⟨(run width).1, ?_⟩
    intro pathIndex suffix finish steps
    obtain ⟨lhs, rhs, reached, mark, marked, paired, _, occurrences, transport, exactPath, returns⟩ := (run width).2 steps
    refine ⟨lhs, rhs, reached, mark, marked, paired, CallbackPrefix.appendComparedOccurrences leading occurrences, transport, exactPath, ?_⟩
    intro pointer cursor active returning
    obtain ⟨_, ⟨bytes, sized, failed⟩, children⟩ := returns pointer cursor active returning
    refine ⟨bytes, sized, ?_⟩
    by_cases misaligned : pointer ≠ ABI.alignTo pointer (ABI.layout destination.width element).alignment
    · rw [ite_eq_left misaligned] at failed ⊢
      exact ⟨by simpa only [List.append_assoc] using CallbackPrefix.appendComparedOccurrences leading failed.2.1, failed.2.2⟩
    · rw [ite_eq_right misaligned] at failed ⊢
      by_cases fits : pointer + entries.length * (ABI.layout destination.width element).size ≤ bytes
      · rw [ite_eq_left fits] at failed ⊢
        refine ⟨?_, ?_⟩
        · intro issue stale
          obtain ⟨peer, _, _, stopped, retained, _⟩ := failed issue stale
          have rebased := CallbackPrefix.appendComparedOccurrences leading stopped
          exact ⟨peer, rebased, retained, covers _ admitted _ _ _ _ cursor rfl rebased⟩
        · intro fresh
          obtain ⟨lhs, rhs, peer, _, paths, retained, frame, _, _, _, _, growth, checkAt, canonAt, body⟩ :=
            children bytes sized (Classical.not_not.mp misaligned) fits fresh
          have rebased := CallbackPrefix.appendComparedOccurrences leading paths
          exact ⟨lhs, rhs, peer, rebased, retained, frame, growth, checkAt, canonAt,
            next pointer bytes suffix lhs rhs cursor peer rebased retained body⟩
      · rw [ite_eq_right fits] at failed ⊢
        exact ⟨by simpa only [List.append_assoc] using CallbackPrefix.appendComparedOccurrences leading failed.2.1, failed.2.2⟩

theorem collectionEntryOccurrences {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {visit : Nat → Nat → Finish grow sig} {path : Nat → Nat → TrailFinish grow sig}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      left right check canon (fun pointer bytes _ => visit pointer bytes))
    (next : ∀ pointer bytes observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs →
      visit pointer bytes lhs rhs cursor peer → path pointer bytes observed lhs rhs cursor peer) :
    LiveCollectionOccurrenceEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming left right seen check canon path sink :=
  collectionEntryOccurrencesWith covers admitted leading run (fun _ _ _ _ _ _ _ paths _ body => next _ _ _ _ _ _ _ paths body)

theorem collectionEntryTransport {destination : RecordDestination} {inst : InstId} {type element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {visit : Nat → Nat → Finish grow sig} {path : Nat → Nat → TrailFinish grow sig}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveCollectionEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      left right check canon (fun pointer bytes _ => visit pointer bytes))
    (next : ∀ pointer bytes observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      visit pointer bytes lhs rhs cursor peer → path pointer bytes observed lhs rhs cursor peer) :
    LiveCollectionOccurrenceEntry profile ready base bindings older destination inst type element entries index output checkNext canonNext
      start incoming left right seen check canon path sink :=
  collectionEntryOccurrencesWith covers admitted (CallbackPrefix.comparedTransportPaths leading) run
    (fun _ _ _ _ _ _ _ _ paths body => next _ _ _ _ _ _ _ (CallbackPrefix.appendComparedTransport leading paths) body)

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
  obtain ⟨store, result, labels, shape, lhs, rhs, _, continued⟩ := run
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

theorem descriptorOccurrences {output : Stored.Lower.Output} {checkNext : ValueCheckNext grow sig output}
    {canonNext : ValueCanonNext grow sig output} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {finish : ValueFinish grow sig output} {visit : TrailFinish grow sig}
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : LiveValueCommit profile ready base bindings output checkNext canonNext finish left right check canon)
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalOccurrenceThen profile ready base bindings start incoming seen visit := by
  obtain ⟨store, result, labels, shape, _, _, paths, continued⟩ := run
  cases result with
  | error reason =>
    have trapped : PayloadPrefix.visible labels = [.trap reason] := CallbackPrefix.visibleLeaf shape
    exact .inl ⟨reason, [], _, _, CallbackPrefix.appendComparedOccurrences leading
      ⟨labels, labels, CallbackPrefix.transportPaths paths, trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok value =>
    obtain ⟨_, _, finished⟩ := continued value rfl
    have reached := CallbackPrefix.appendComparedOccurrences leading
      ⟨labels, labels, CallbackPrefix.transportPaths paths, rfl, rfl, rfl⟩
    exact .inr ⟨PayloadPrefix.visible labels, _, _, check, canon, reached, next value _ _ _ _ _ reached rfl finished⟩

theorem descriptorTransport {output : Stored.Lower.Output} {checkNext : ValueCheckNext grow sig output}
    {canonNext : ValueCanonNext grow sig output} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {finish : ValueFinish grow sig output} {visit : TrailFinish grow sig}
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveValueCommit profile ready base bindings output checkNext canonNext finish left right check canon)
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalTransportThen profile ready base bindings start incoming seen visit := by
  obtain ⟨store, result, labels, shape, _, _, paths, continued⟩ := run
  cases result with
  | error reason =>
    have trapped : PayloadPrefix.visible labels = [.trap reason] := CallbackPrefix.visibleLeaf shape
    exact .inl ⟨reason, [], _, _, CallbackPrefix.appendComparedTransport leading
      ⟨labels, labels, paths, trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok value =>
    obtain ⟨_, _, finished⟩ := continued value rfl
    have reached := CallbackPrefix.appendComparedTransport leading ⟨labels, labels, paths, rfl, rfl, rfl⟩
    exact .inr ⟨_, _, _, check, canon, reached, next value _ _ _ _ _ reached finished⟩

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
    obtain ⟨keyRead, keyQuiet, keyTracks, store, result, lhsLabels, rhsLabels, lhs, rhs, same, _, tail⟩ := run
    have atKey := canonicalRead leading (fun depth => keyTracks (.active 0 depth)) keyQuiet
    cases result with
    | error reason =>
      obtain ⟨before, trapped⟩ := tail
      exact .inl ⟨reason, before, _, _, CallbackPrefix.appendComparedPaths atKey
        ⟨lhsLabels, rhsLabels, lhs, rhs.steps, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
    | ok done =>
      cases done
      obtain ⟨lhsTracks, rhsTracks, valueRead, valueQuiet, valueTracks, body⟩ := tail
      have atValue := canonicalRead (CallbackPrefix.appendComparedSlots atKey
        ⟨lhsLabels, rhsLabels, lhsTracks, rhsTracks, rfl, same.symm⟩) (fun depth => valueTracks (.active 0 depth)) valueQuiet
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
  exact ⟨read, CallbackPrefix.liveElementsPathsFrom lift (canonicalRead leading (fun depth => read (.active 0 depth)) rfl)
    same body (sink.nested _ admitted index) next⟩

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
    {history : Trace grow sig → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) → Prop}
    (paired : ∀ type raw, (type, raw) ∈ fields → ∃ trail, (type, trail) ∈ paths ∧
      LiftsFieldPathsWith history raw trail sink) :
    LiftsFieldPathsWith history (aggregateChild fields) (selectPathField paths) sink := by
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

theorem listOccurrencePaths {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {finish : ValueFinish grow sig output} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index output
      checkNext canonNext left right check canon
      (fun pointer bytes _ => liveListTail profile ready base bindings destination inst element entries index output child checkNext canonNext finish pointer bytes))
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index output
      checkNext canonNext start incoming left right seen check canon
      (liveListTailPaths destination inst element entries index output paths checkNext canonNext
        (fun observed _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming observed visit)) sink := by
  apply collectionEntryOccurrences covers admitted leading run
  intro pointer bytes observed lhs rhs cursor peer history body
  have shared : lhs.store = rhs.store := by
    obtain ⟨_, _, _, _, _, shared⟩ := history
    exact shared
  refine CallbackPrefix.liveElementsPathsFrom lift history shared body (sink.nested _ admitted index) ?_
  intro _ _ _ _ _ historyAtDescriptor _ published
  exact descriptorOccurrences historyAtDescriptor published next

theorem listTransportPaths {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {finish : ValueFinish grow sig output} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (lift : LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveCollectionEntry profile ready base bindings older destination inst (.list element) element entries index output
      checkNext canonNext left right check canon
      (fun pointer bytes _ => liveListTail profile ready base bindings destination inst element entries index output child checkNext canonNext finish pointer bytes))
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.list element) element entries index output
      checkNext canonNext start incoming left right seen check canon
      (liveListTailPaths destination inst element entries index output paths checkNext canonNext
        (fun observed _ _ _ _ => LocalTransportThen profile ready base bindings start incoming observed visit)) sink := by
  apply collectionEntryTransport covers admitted leading run
  intro pointer bytes observed lhs rhs cursor peer history body
  refine CallbackPrefix.liveElementsPathsFrom lift history history.choose_spec.choose_spec.2.2.2 body (sink.nested _ admitted index) ?_
  intro _ _ _ _ _ historyAtDescriptor _ published
  exact descriptorTransport historyAtDescriptor published next

private theorem mapEntryOccurrences {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType}
    {element : Stored.TypeOf} {output : Stored.Lower.Output} {field value : Field} {index pointer : Nat}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : liveCollectionMapEntry profile ready base bindings older destination inst key element output field value index pointer
      child checkNext canonNext finish left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    mapEntryOccurrencePaths profile ready base bindings older destination inst key element output start incoming paths
      field value index pointer checkNext canonNext visit seen left right check canon := by
  unfold liveCollectionMapEntry at run
  unfold mapEntryOccurrencePaths
  split at run
  · rename_i stringKey
    subst key
    exact CallbackPrefix.stringMapEntryOccurrences lift leading run admitted next
  · rename_i notString
    simp only [notString, ↓reduceIte]
    obtain ⟨_, keyQuiet, keyTracks, store, result, lhsLabels, rhsLabels, _, _, same, occurrences, tail⟩ := run
    have shared : left.store = right.store := by
      obtain ⟨_, _, _, _, _, shared⟩ := leading
      exact shared
    have atKey := CallbackPrefix.appendQuietCanonicalRead leading keyTracks keyQuiet shared
    cases result with
    | error reason =>
      obtain ⟨prior, trapped⟩ := tail
      exact .inl ⟨reason, prior, _, _, CallbackPrefix.appendComparedOccurrences atKey
        ⟨lhsLabels, rhsLabels, CallbackPrefix.transportPaths occurrences, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
    | ok complete =>
      cases complete
      obtain ⟨_, _, _, valueQuiet, valueTracks, body⟩ := tail
      have written := CallbackPrefix.appendComparedOccurrences (after := PayloadPrefix.visible lhsLabels) atKey
        ⟨lhsLabels, rhsLabels, CallbackPrefix.transportPaths occurrences, rfl, same.symm, rfl⟩
      have atValue := CallbackPrefix.appendQuietCanonicalRead written valueTracks valueQuiet rfl
      exact .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, atValue,
        lift value 1 _ _ _ check canon _ canonNext finish visit _ body atValue rfl (sink.nested _ admitted index) next⟩

private theorem mapElementsOccurrences {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType}
    {element : Stored.TypeOf} {output : Stored.Lower.Output} {entries : List Field} {index pointer : Nat}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : liveMapElementsWith (liveCollectionMapEntry profile ready base bindings older destination inst key element output)
      destination inst key element output child checkNext canonNext finish entries index pointer left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveMapElementsPaths (mapEntryOccurrencePaths profile ready base bindings older destination inst key element output start incoming paths)
      destination inst key element output checkNext canonNext visit entries index pointer seen left right check canon := by
  induction entries generalizing index pointer seen left right check canon with
  | nil => exact next seen left right check canon leading run
  | cons item rest ih =>
    obtain ⟨payload, value, shape, entry⟩ := run
    exact ⟨payload, value, shape, mapEntryOccurrences lift leading entry admitted
      (fun _ _ _ _ _ history _ tail => ih history tail)⟩

theorem mapOccurrencePaths {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType} {element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {finish : ValueFinish grow sig output} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (run : LiveCollectionEntry profile ready base bindings older destination inst (.map key element)
      (.record (ABI.mapEntryFields key element)) entries index output checkNext canonNext left right check canon
      (fun pointer bytes _ => liveMapTailWith profile ready base bindings
        (liveCollectionMapEntry profile ready base bindings older destination inst key element output)
        destination inst key element entries index output child checkNext canonNext finish pointer bytes))
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element)
      (.record (ABI.mapEntryFields key element)) entries index output checkNext canonNext start incoming left right seen check canon
      (liveMapTailPaths (mapEntryOccurrencePaths profile ready base bindings older destination inst key element output start incoming paths)
        destination inst key element entries index output checkNext canonNext
        (fun observed _ _ _ _ => LocalOccurrenceThen profile ready base bindings start incoming observed visit)) sink := by
  apply collectionEntryOccurrences covers admitted leading run
  intro pointer bytes observed lhs rhs cursor peer history body
  refine mapElementsOccurrences lift history body (sink.nested _ admitted index) ?_
  intro _ _ _ _ _ atDescriptor published
  exact descriptorOccurrences atDescriptor published next

private theorem mapEntryTransport {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType}
    {element : Stored.TypeOf} {output : Stored.Lower.Output} {field value : Field} {index pointer : Nat}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : liveCollectionMapEntry profile ready base bindings older destination inst key element output field value index pointer
      child checkNext canonNext finish left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    mapEntryTransportPaths profile ready base bindings older destination inst key element output start incoming paths
      field value index pointer checkNext canonNext visit seen left right check canon := by
  unfold liveCollectionMapEntry at run
  unfold mapEntryTransportPaths
  split at run
  · rename_i stringKey
    subst key
    simp only [↓reduceIte]
    refine CallbackPrefix.stringMapEntryTransport leading run ?_
    intro ptr observed lhs rhs cursor peer history body
    exact lift value 1 ptr lhs rhs cursor peer _ canonNext finish visit observed body history
      history.choose_spec.choose_spec.2.2.2 (sink.nested _ admitted index) next
  · rename_i notString
    simp only [notString, ↓reduceIte]
    obtain ⟨_, keyQuiet, keyTracks, _, result, lhsLabels, rhsLabels, _, _, same, movement, tail⟩ := run
    have atKey := CallbackPrefix.appendQuietCanonicalTransport leading keyTracks keyQuiet leading.choose_spec.choose_spec.2.2.2
    cases result with
    | error reason =>
      obtain ⟨prior, trapped⟩ := tail
      exact .inl ⟨reason, prior, _, _, CallbackPrefix.appendComparedTransport atKey
        ⟨lhsLabels, rhsLabels, movement, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
    | ok complete =>
      cases complete
      obtain ⟨_, _, _, quiet, read, body⟩ := tail
      have written := CallbackPrefix.appendComparedTransport (more := PayloadPrefix.visible lhsLabels) atKey
        ⟨lhsLabels, rhsLabels, movement, rfl, same.symm, rfl⟩
      have atValue := CallbackPrefix.appendQuietCanonicalTransport written read quiet rfl
      exact .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, atValue,
        lift value 1 _ _ _ check canon _ canonNext finish visit _ body atValue rfl (sink.nested _ admitted index) next⟩

private theorem mapElementsTransport {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType} {element : Stored.TypeOf}
    {output : Stored.Lower.Output} {entries : List Field} {index pointer : Nat}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : liveMapElementsWith (liveCollectionMapEntry profile ready base bindings older destination inst key element output)
      destination inst key element output child checkNext canonNext finish entries index pointer left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveMapElementsPaths (mapEntryTransportPaths profile ready base bindings older destination inst key element output start incoming paths)
      destination inst key element output checkNext canonNext visit entries index pointer seen left right check canon := by
  induction entries generalizing index pointer seen left right check canon with
  | nil => exact next seen left right check canon leading run
  | cons item rest ih =>
    obtain ⟨payload, value, shape, entry⟩ := run
    exact ⟨payload, value, shape, mapEntryTransport lift leading entry admitted
      (fun _ _ _ _ _ history _ tail => ih history tail)⟩

theorem mapTransportPaths {destination : RecordDestination} {inst : InstId} {key : WIT.KeyType} {element : Stored.TypeOf}
    {entries : List Field} {index : Nat} {output : Stored.Lower.Output}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : ValueCheckNext grow sig output} {canonNext : ValueCanonNext grow sig output}
    {finish : ValueFinish grow sig output} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (lift : LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveCollectionEntry profile ready base bindings older destination inst (.map key element)
      (.record (ABI.mapEntryFields key element)) entries index output checkNext canonNext left right check canon
      (fun pointer bytes _ => liveMapTailWith profile ready base bindings
        (liveCollectionMapEntry profile ready base bindings older destination inst key element output)
        destination inst key element entries index output child checkNext canonNext finish pointer bytes))
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ value observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs →
      finish value lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LiveCollectionOccurrenceEntry profile ready base bindings older destination inst (.map key element)
      (.record (ABI.mapEntryFields key element)) entries index output checkNext canonNext start incoming left right seen check canon
      (liveMapTailPaths (mapEntryTransportPaths profile ready base bindings older destination inst key element output start incoming paths)
        destination inst key element entries index output checkNext canonNext
        (fun observed _ _ _ _ => LocalTransportThen profile ready base bindings start incoming observed visit)) sink := by
  apply collectionEntryTransport covers admitted leading run
  intro pointer bytes observed lhs rhs cursor peer history body
  refine mapElementsTransport lift history body (sink.nested _ admitted index) ?_
  intro _ _ _ _ _ atDescriptor published
  exact descriptorTransport atDescriptor published next

private theorem fixedOccurrencePaths {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {entries : List Field} {index address : Nat} {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldOccurrencePaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrencePaths profile ready base bindings start incoming seen left right)
    (same : left.store = right.store)
    (run : LiveFixedThen profile ready base bindings destination inst child element entries index address checkNext canonNext finish
      left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrencePaths profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveFixedPaths profile ready base bindings destination inst paths element entries index address checkNext canonNext visit
      seen left right check canon := by
  obtain ⟨read, body⟩ := run
  have reached := CallbackPrefix.appendComparedOccurrences (after := []) leading
    ⟨[], [.tau], fun mark => ⟨mark, .done _ _, CallbackPrefix.unchangedTrail read mark⟩, rfl, rfl, same⟩
  rw [List.append_nil] at reached
  exact ⟨read, CallbackPrefix.liveElementsPathsFrom lift reached same body (sink.nested _ admitted index) next⟩

private theorem emptyOccurrenceLift :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (fun _ _ _ _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ _ _ => False) sink := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ impossible
  exact impossible.elim

private theorem variantOccurrenceLift (destination : RecordDestination) (inst : InstId)
    (cases : List (String × Option Stored.TypeOf)) (tag : Nat)
    (arms : ∀ name type, (name, some type) ∈ cases → LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type) sink) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveVariantArm profile ready base bindings older destination inst cases tag)
      (structuralVariantOccurrencePaths profile ready base bindings older destination inst start incoming sink cases tag) sink := by
  induction cases generalizing tag with
  | nil => cases tag <;> exact emptyOccurrenceLift
  | cons field rest ih =>
    obtain ⟨name, arm⟩ := field
    cases tag with
    | zero => cases arm with
      | none => exact emptyOccurrenceLift
      | some type => exact arms name type (List.mem_cons_self ..)
    | succ tag =>
      simpa only [liveVariantArm, structuralVariantOccurrencePaths] using
        (ih tag (fun name type member => arms name type (List.mem_cons_of_mem _ member)))

private theorem tupleOccurrenceLift (destination : RecordDestination) (inst : InstId) (types : List Stored.TypeOf)
    (children : ∀ type ∈ types, LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type) sink) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (aggregateChild (liveTupleFields profile ready base bindings older destination inst types))
      (selectPathField (structuralTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink types)) sink := by
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

private theorem recordOccurrencePaths (destination : RecordDestination) (inst : InstId) (fields : List (String × Stored.TypeOf)) :
    structuralRecordOccurrencePaths profile ready base bindings older destination inst start incoming sink fields =
      structuralTupleOccurrencePaths profile ready base bindings older destination inst start incoming sink (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    cases field
    simp only [structuralRecordOccurrencePaths, List.map_cons, structuralTupleOccurrencePaths, ih]

theorem structuralFieldOccurrences {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming) (family : StructuralMemoryOccurrenceType type) :
    LiftsFieldOccurrencePaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (structuralMemoryOccurrencePaths profile ready base bindings older destination inst start incoming sink type) sink := by
  induction family with
  | leaf nominal =>
    have lifted := CallbackPrefix.leafOccurrenceLift (destination := destination) (inst := inst) (older := older) covers (.inl nominal)
    cases nominal <;> exact lifted
  | data data =>
    have lifted := CallbackPrefix.leafOccurrenceLift (destination := destination) (inst := inst) (older := older) covers (.inr (.inl data))
    cases data with
    | @primitive primitive notString => cases primitive <;> exact lifted
    | enum | flags => exact lifted
  | string =>
    exact CallbackPrefix.leafOccurrenceLift (destination := destination) (inst := inst) (older := older) covers (.inr (.inr rfl))
  | list _ child =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨entries, shape, body⟩ := run
    exact ⟨entries, shape, listOccurrencePaths covers child leading body admitted (fun () => next)⟩
  | map _ child =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨entries, shape, body⟩ := run
    exact ⟨entries, shape, mapOccurrencePaths covers child leading body admitted (fun () => next)⟩
  | fixed _ child =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨entries, shape, body⟩ := run
    exact ⟨entries, shape, fixedOccurrencePaths child leading same body admitted next⟩
  | option _ child =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨tag, selected, shape, body⟩ := run
    refine ⟨tag, selected, shape, ?_⟩
    cases selected <;> exact CallbackPrefix.sumOccurrencePathsFrom (fun _ => child) leading body admitted next
  | @result success failure _ _ okChild errChild =>
    cases success <;> cases failure <;>
      intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    all_goals
      obtain ⟨tag, selected, shape, body⟩ := run
      refine ⟨tag, selected, shape, ?_⟩
      by_cases ok : tag = 0 <;> simp only [ok, ↓reduceIte] at body ⊢ <;> cases selected <;> first
        | exact CallbackPrefix.sumOccurrencePathsFrom (fun _ => emptyOccurrenceLift) leading body admitted next
        | exact CallbackPrefix.sumOccurrencePathsFrom (fun _ => okChild _ rfl) leading body admitted next
        | exact CallbackPrefix.sumOccurrencePathsFrom (fun _ => errChild _ rfl) leading body admitted next
  | @variant cases _ arms =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨tag, selected, shape, body⟩ := run
    refine ⟨tag, selected, shape, ?_⟩
    cases selected <;> exact CallbackPrefix.sumOccurrencePathsFrom (fun _ => variantOccurrenceLift destination inst cases tag arms) leading body admitted next
  | @record fields _ children =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨items, shape, body⟩ := run
    have lift := tupleOccurrenceLift destination inst (fields.map Prod.snd) (fun type member => by
      obtain ⟨⟨name, schema⟩, present, rfl⟩ := List.mem_map.mp member
      exact children name schema present)
    rw [← CallbackPrefix.recordTable destination inst, ← recordOccurrencePaths destination inst] at lift
    exact ⟨items, shape, CallbackPrefix.aggregateOccurrencePathsFrom lift leading same body admitted next⟩
  | @tuple types _ children =>
    intro item index address left right check canon checkNext canonNext finish visit before run leading same admitted next
    obtain ⟨items, shape, body⟩ := run
    exact ⟨items, shape, CallbackPrefix.aggregateOccurrencePathsFrom (tupleOccurrenceLift destination inst types children) leading same body admitted next⟩

private theorem fixedTransport {destination : RecordDestination} {inst : InstId} {element : Stored.TypeOf}
    {entries : List Field} {index address : Nat} {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (same : left.store = right.store)
    (run : LiveFixedThen profile ready base bindings destination inst child element entries index address checkNext canonNext finish
      left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveFixedPaths profile ready base bindings destination inst paths element entries index address checkNext canonNext visit
      seen left right check canon := by
  obtain ⟨read, body⟩ := run
  have reached := CallbackPrefix.appendQuietCanonicalTransport leading read rfl same
  exact ⟨read, CallbackPrefix.liveElementsPathsFrom lift reached same body (sink.nested _ admitted index) next⟩

private theorem sumTransport {destination : RecordDestination} {inst : InstId}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {arms : List (Option Stored.TypeOf)} {selected : Option Field} {index address : Nat}
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : selected.isSome = true → LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (run : LiveSumThen profile ready base bindings destination inst child arms selected index address
      checkNext canonNext finish left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    LocalTransportThen profile ready base bindings start incoming seen
      (match selected with
      | none => visit
      | some item => paths item 0 (PayloadPrefix.sumPayloadAddress destination.width arms address)
          (aggregateNext index checkNext) canonNext visit) := by
  obtain ⟨store, result, lhsLabels, rhsLabels, _, _, same, trails, tail⟩ := run
  cases result with
  | error reason =>
    obtain ⟨prefixLabels, trapped⟩ := tail
    exact .inl ⟨reason, prefixLabels, _, _, CallbackPrefix.appendComparedTransport leading
      ⟨lhsLabels, rhsLabels, trails, same.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok result =>
    cases result
    obtain ⟨_, _, done⟩ := tail
    have reached := CallbackPrefix.appendComparedTransport leading ⟨lhsLabels, rhsLabels, trails, rfl, same.symm, rfl⟩
    refine .inr ⟨PayloadPrefix.visible lhsLabels, _, _, check, canon, reached, ?_⟩
    cases selected with
    | none => exact next _ _ _ _ _ reached rfl done
    | some item =>
      exact lift rfl item 0 _ _ _ check canon _ canonNext finish visit _ done reached rfl
        (sink.nested _ admitted index) next

private theorem emptyTransportLift :
    LiftsFieldTransportPaths profile ready base bindings start incoming
      (fun _ _ _ _ _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ _ _ _ _ _ => False) sink := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ impossible
  exact impossible.elim

private theorem variantTransportLift (destination : RecordDestination) (inst : InstId)
    (cases : List (String × Option Stored.TypeOf)) (tag : Nat)
    (arms : ∀ name type, (name, some type) ∈ cases → LiftsFieldTransportPaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type) sink) :
    LiftsFieldTransportPaths profile ready base bindings start incoming
      (liveVariantArm profile ready base bindings older destination inst cases tag)
      (recursiveVariantTransportPaths profile ready base bindings older destination inst start incoming sink cases tag) sink := by
  induction cases generalizing tag with
  | nil => cases tag <;> exact emptyTransportLift
  | cons field rest ih =>
    obtain ⟨name, arm⟩ := field
    cases tag with
    | zero => cases arm with
      | none => exact emptyTransportLift
      | some type => exact arms name type (List.mem_cons_self ..)
    | succ tag =>
      simpa only [liveVariantArm, recursiveVariantTransportPaths] using
        (ih tag (fun name type member => arms name type (List.mem_cons_of_mem _ member)))

private theorem tupleTransportLift (destination : RecordDestination) (inst : InstId) (types : List Stored.TypeOf)
    (children : ∀ type ∈ types, LiftsFieldTransportPaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type) sink) :
    LiftsFieldTransportPaths profile ready base bindings start incoming
      (aggregateChild (liveTupleFields profile ready base bindings older destination inst types))
      (selectPathField (recursiveTupleTransportPaths profile ready base bindings older destination inst start incoming sink types)) sink := by
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

private theorem recordTransportPaths (destination : RecordDestination) (inst : InstId) (fields : List (String × Stored.TypeOf)) :
    recursiveRecordTransportPaths profile ready base bindings older destination inst start incoming sink fields =
      recursiveTupleTransportPaths profile ready base bindings older destination inst start incoming sink (fields.map Prod.snd) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    cases field
    simp only [recursiveRecordTransportPaths, List.map_cons, recursiveTupleTransportPaths, ih]

private theorem aggregateTransport {destination : RecordDestination} {inst : InstId}
    {child : FieldComparison grow sig} {paths : TrailFieldComparison grow sig}
    {checkNext : CheckNext grow sig} {canonNext : CanonNext grow sig} {finish : Finish grow sig} {visit : TrailFinish grow sig}
    {items : List Field} {index address : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (lift : LiftsFieldTransportPaths profile ready base bindings start incoming child paths sink)
    (leading : ComparedOccurrenceTransport profile ready base bindings start incoming seen left right)
    (same : left.store = right.store)
    (run : LiveAggregateThen profile ready base bindings destination inst child items index address checkNext canonNext finish
      left right check canon)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (next : ∀ observed lhs rhs cursor peer,
      ComparedOccurrenceTransport profile ready base bindings start incoming observed lhs rhs → lhs.store = rhs.store →
      finish lhs rhs cursor peer → visit observed lhs rhs cursor peer) :
    liveAggregatePaths profile ready base bindings destination inst paths items index address checkNext canonNext visit
      seen left right check canon := by
  obtain ⟨read, body⟩ := run
  have placement : ComparedOccurrenceTransport profile ready base bindings left right []
      (enterAggregate destination inst items index address left check checkNext) right :=
    ⟨[.tau], [], CallbackPrefix.stationaryTransport read (fun place => .done right place), rfl, rfl, same⟩
  have reached := CallbackPrefix.appendComparedTransport leading placement
  rw [List.append_nil] at reached
  exact ⟨CallbackPrefix.comparedTransportPaths placement,
    CallbackPrefix.replayBetweenTransportFrom lift reached body (sink.nested _ admitted index) next⟩

theorem recursiveAllocatingTransport {destination : RecordDestination} {inst : InstId} {type : Stored.TypeOf}
    (covers : sink.CoversOccurrences profile ready base bindings start incoming)
    (family : RecursiveAllocatingTransportType type) :
    LiftsFieldTransportPaths profile ready base bindings start incoming
      (liveCollectionField profile ready base bindings older destination inst type)
      (recursiveAllocatingTransportPaths profile ready base bindings older destination inst start incoming sink type) sink := by
  induction family with
  | leaf nominal =>
    cases nominal <;> intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ admitted next <;>
      exact CallbackPrefix.handleValueTransport leading run covers admitted (fun () => next)
  | data data =>
    cases data with
    | @primitive primitive nonstring =>
      cases primitive <;> first
        | exact (nonstring rfl).elim
        | intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ _ next
          exact CallbackPrefix.localFieldTransport leading run next
    | enum | flags =>
      intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ _ next
      exact CallbackPrefix.localFieldTransport leading run next
  | string =>
    intro _ _ _ _ _ _ _ _ _ _ _ before run leading _ _ next
    obtain ⟨str, shape, body⟩ := run
    refine ⟨str, shape, CallbackPrefix.stringValueOccurrencePathsFrom (CallbackPrefix.comparedTransportPaths leading)
      ⟨before, leading⟩ body ?_⟩
    intro _ _ _ _ _ _ published _ transported
    obtain ⟨observed, reached⟩ := transported
    exact ⟨observed, CallbackPrefix.localFieldTransport reached published next⟩
  | list _ child =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ admitted next
    obtain ⟨entries, shape, body⟩ := run
    exact ⟨entries, shape, listTransportPaths covers child leading body admitted
      (fun () observed lhs rhs cursor peer paths => next observed lhs rhs cursor peer paths paths.choose_spec.choose_spec.2.2.2)⟩
  | map _ child =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ admitted next
    obtain ⟨entries, shape, body⟩ := run
    exact ⟨entries, shape, mapTransportPaths covers child leading body admitted
      (fun () observed lhs rhs cursor peer paths => next observed lhs rhs cursor peer paths paths.choose_spec.choose_spec.2.2.2)⟩
  | fixed _ child =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ run leading same admitted next
    obtain ⟨entries, shape, body⟩ := run
    exact ⟨entries, shape, fixedTransport child leading same body admitted next⟩
  | option _ child =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ admitted next
    obtain ⟨tag, selected, shape, body⟩ := run
    refine ⟨tag, selected, shape, ?_⟩
    cases selected <;> exact sumTransport (fun _ => child) leading body admitted next
  | @result success failure _ _ okChild errChild =>
    cases success <;> cases failure <;>
      intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ admitted next
    all_goals
      obtain ⟨tag, selected, shape, body⟩ := run
      refine ⟨tag, selected, shape, ?_⟩
      by_cases ok : tag = 0 <;> simp only [ok, ↓reduceIte] at body ⊢ <;> cases selected <;> first
        | exact sumTransport (fun _ => emptyTransportLift) leading body admitted next
        | exact sumTransport (fun _ => okChild _ rfl) leading body admitted next
        | exact sumTransport (fun _ => errChild _ rfl) leading body admitted next
  | @variant cases _ arms =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ run leading _ admitted next
    obtain ⟨tag, selected, shape, body⟩ := run
    refine ⟨tag, selected, shape, ?_⟩
    cases selected <;> exact sumTransport (fun _ => variantTransportLift _ _ cases tag arms) leading body admitted next
  | @record fields _ children =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ run leading same admitted next
    obtain ⟨items, shape, body⟩ := run
    have lift := tupleTransportLift destination inst (fields.map Prod.snd) (fun type member => by
      obtain ⟨⟨name, schema⟩, present, rfl⟩ := List.mem_map.mp member
      exact children name schema present)
    rw [← CallbackPrefix.recordTable destination inst, ← recordTransportPaths destination inst] at lift
    exact ⟨items, shape, aggregateTransport lift leading same body admitted next⟩
  | @tuple types _ children =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ run leading same admitted next
    obtain ⟨items, shape, body⟩ := run
    exact ⟨items, shape, aggregateTransport (tupleTransportLift destination inst types children) leading same body admitted next⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.RecursiveTrails
