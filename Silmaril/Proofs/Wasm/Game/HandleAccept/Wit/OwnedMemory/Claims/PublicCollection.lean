module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.PublicCollection

private theorem chain {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch : Call E → P E Host (Ret E)} {first middle last : Config E Host} {front back : List (Label E Host)}
    (lhs : Steps profile ready dispatch first front middle) (rhs : Steps profile ready dispatch middle back last) :
    Steps profile ready dispatch first (front ++ back) last := by
  induction lhs with
  | refl => exact rhs
  | cons step _ ih => exact .cons step (ih rhs)

private theorem visibleAppend {E : CoreEngine} {Host : Type} (front back : List (Label E Host)) :
    visible (front ++ back) = visible front ++ visible back := List.filter_append ..

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem prependCut {Result : Type} {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {left left' right afterPop : State grow sig} {cursor : Cursor (E := core3 grow) (HostState sig)}
    {checkNext : Except Endpoints.RecordLower.Issue Result → Session grow sig (Ret (core3 grow))}
    {canonNext : Result → Session grow sig (Ret (core3 grow))} {front seen}
    (entry : Steps profile ready (specDispatch ready (host bindings)) left front left') (silent : visible front = [])
    (cut : CollectionCut profile ready bindings first second left' right afterPop cursor checkNext canonNext seen) :
    CollectionCut profile ready bindings first second left right afterPop cursor checkNext canonNext seen := by
  rcases cut with ⟨canonCursor, thread, reaches⟩ | ⟨leftLabels, rightLabels, other, lhs, rhs, paired, lhsSeen, rhsSeen⟩
  · exact .inl ⟨canonCursor, thread, Reaches.prepend entry (.refl _) silent reaches⟩
  · exact .inr ⟨front ++ leftLabels, rightLabels, other, chain entry lhs, rhs, paired,
      by rw [visibleAppend, silent, List.nil_append, lhsSeen], rhsSeen⟩

theorem parked (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings)
    {children : State grow sig → Nat → Prop}
    (compare : ∀ reached pointer, children reached pointer → site.TailRule profile ready bindings reached pointer) :
    Outcome site profile ready bindings next children := by
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  have rootLinked : site.toRoot.Linked bindings := ⟨linked.parked, linked.calling, linked.linked, linked.caller,
    linked.mayLeave, linked.destination, linked.selected, linked.admitted, linked.compiled⟩
  rcases site.toRoot.parked (profile := profile) (ready := ready) rootLinked with
    ⟨issue, silent, stopped⟩ | ⟨reason, count, placed, halted⟩ | ⟨silent, _, prepared, reached, _⟩
  · exact .refused issue silent stopped.steps
  · exact .placementTrap reason count placed halted.steps
  · have canonAt : (site.reference next).ctl = site.cursor.control
        (CanonicalTree.field Limits.spec Quirks.none (site.destination.context site.inst) site.destination.width
          site.field site.route.output >>= next) := site.toRoot.reference_at rootLinked next
    have width := site.destination.check_width site.start.store linked.destination
    have sizePresent := (Silmaril.Wasm.Component.Engine.Core3.memAddrType?_isSome_iff
      (s := site.start.store.core) (m := site.destination.memory)).mp (show
        ((core3 grow).memAddrType? site.start.store.core site.destination.memory).isSome by
      simp [width])
    obtain ⟨bytes, sized⟩ := Option.isSome_iff_exists.mp sizePresent
    obtain ⟨lhs, rhs, paired⟩ := collection_install (profile := profile) (ready := ready) (dispatch := dispatch)
      site.destination site.inst site.type site.element site.entries site.route.output 0 (site.withBody site.checkedBody)
      (site.reference next) site.cursor site.reply next rfl width linked.mode prepared rfl canonAt
    refine .installed (by rw [visibleAppend, silent]; rfl) (by rfl) (chain reached.steps lhs) rhs paired ?_
    intro last seen path cursor pointer reachedReturn children
    exact prependCut reached.steps silent (Prefix.collection site.destination site.inst site.type site.element
      site.entries site.route.output 0 pointer site.cursor cursor site.reply next rfl (.refl _) linked.destination sized
      linked.mode prepared rfl canonAt path reachedReturn (compare last pointer children))

private theorem dynamicEntries {type schema element : TypeOf} {entries : List Field}
    (layoutMatch : Field.LayoutMatches (.dynamic type element entries) schema) : Field.EntriesMatch entries element := by
  cases layoutMatch with
  | list children => exact children
  | map children => exact children

theorem parkedScalars (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings)
    (primitive : WIT.Primitive) (element : site.element = .prim primitive) (nonString : primitive ≠ .string) :
    Outcome site profile ready bindings next (fun _ _ => True) := by
  obtain ⟨plan, compiled⟩ := linked.compiled
  have layoutMatch := Record.preflightValue_layout _ _ _ _ _ plan compiled
  unfold Site.field at layoutMatch
  rw [element] at layoutMatch
  apply parked site profile ready bindings next linked
  intro reached pointer _ reference bytes width sized
  have compared := CollectionTailAt.scalar_entries (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host (grow := grow) bindings)) site.destination site.inst primitive nonString
    site.entries (dynamicEntries layoutMatch) site.route.output 0 pointer bytes reached reference width sized
  simpa only [Site.area, element] using compared

theorem parkedLocalEntries (site : Site grow sig) (profile : ProfileKind) (ready : HostReady (HostState sig))
    (bindings : List (Binding sig)) (next : site.ReferenceNext) (linked : site.Linked bindings)
    (fragment : ∀ item ∈ site.entries, LocalMemory item) : Outcome site profile ready bindings next (fun _ _ => True) := by
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
  unfold Site.field at matched
  apply parked site profile ready bindings next linked
  intro reached pointer _ reference bytes width sized
  apply CollectionTailAt.memory_entries site.destination site.inst site.element site.entries _ site.route.output 0
    pointer bytes reached reference width sized
  intro item member
  exact MemoryChildRule.local_memory site.destination site.inst (fragment item member)
    (entries_match_of_mem (dynamicEntries matched) member)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicCollection
