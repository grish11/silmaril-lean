module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Width.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.ABI.Layout.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

theorem slotsMap (mode : Track) (width : AddrType) {premise target : Field → Nat → Prop}
    (convert : ∀ item address, premise item address → target item address) (items : List Field) (cursor : Nat)
    (slots : mode.Slots width premise items cursor) : mode.Slots width target items cursor := by
  induction items generalizing cursor with
  | nil => exact trivial
  | cons item rest ih => exact ⟨convert item _ slots.1, ih _ slots.2⟩

private theorem fieldSlots (width : AddrType) (rule : Field → Nat → Prop) (items : List Field) (base : Nat)
    (placed : ∀ (index : Nat) item address, items[index]? = some item →
      (fieldOffsets base (items.map fun field => layout width field.type))[index]? = some address → rule item address) :
    Track.fields.Slots width rule items base := by
  induction items generalizing base with
  | nil => exact trivial
  | cons item rest ih =>
    refine ⟨placed 0 item _ rfl rfl, ih _ ?_⟩
    intro index child address found offset
    exact placed (index + 1) child address found offset

theorem aggregateSlots (width : AddrType) {type : TypeOf} {items : List Field} {bytes base : Nat}
    (matched : Field.LayoutMatches (.aggregate type items) type)
    (aligned : base % (layout width type).alignment.bytes = 0) (bounds : base + (layout width type).size ≤ bytes)
    (rule : Field → Nat → Prop) (child : ∀ item ∈ items, ∀ address, SlotFits width bytes item address → rule item address) :
    Track.fields.Slots width rule items base := by
  have compiled := compiled_aggregate_layout width matched
  rw [compiled] at aligned bounds
  apply fieldSlots
  intro index item address found offset
  have shape : (items.map fun field => layout width field.type)[index]? = some (layout width item.type) := by
    simp only [List.getElem?_map, found, Option.map_some]
  obtain ⟨_, modulo, fits⟩ := recordLayout_field_fits _ base index address _ (Nat.dvd_of_mod_eq_zero aligned) shape offset
  exact child item (List.mem_of_getElem? found) address ⟨modulo, fits.trans bounds⟩

theorem elementSlots (width : AddrType) {element : TypeOf} {items : List Field} {bytes base : Nat}
    (matched : Field.EntriesMatch items element) (aligned : base = alignTo base (layout width element).alignment)
    (bounds : base + items.length * (layout width element).size ≤ bytes)
    (rule : Field → Nat → Prop) (child : ∀ item ∈ items, ∀ address, SlotFits width bytes item address → rule item address) :
    (Track.elements (layout width element).size).Slots width rule items base := by
  let area := layout width element
  have baseDiv : area.alignment.bytes ∣ base :=
    ⟨(base + area.alignment.bytes - 1) / area.alignment.bytes, aligned.trans (Nat.mul_comm ..)⟩
  have strideDiv : area.alignment.bytes ∣ area.size := ⟨area.units, Nat.mul_comm ..⟩
  clear aligned
  induction items generalizing base with
  | nil => exact trivial
  | cons item rest ih =>
    cases matched with
    | cons head tail =>
      have layoutEq : layout width item.type = area := congrArg (layout width) head.type_eq
      have positioned : SlotFits width bytes item base := by
        unfold SlotFits
        rw [layoutEq]
        refine ⟨Nat.mod_eq_zero_of_dvd baseDiv, ?_⟩
        simpa only [List.length_cons, Nat.succ_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
          (Nat.add_le_add_left (Nat.mul_le_mul_right area.size (Nat.succ_le_succ (Nat.zero_le rest.length))) base).trans bounds
      refine ⟨child item (List.mem_cons_self ..) base positioned, ih tail ?_ ?_ (Nat.dvd_add baseDiv strideDiv)⟩
      · simpa only [List.length_cons, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bounds
      · exact fun entry member => child entry (List.mem_cons_of_mem _ member)

private theorem focusStep (mode : Track) (destination : RecordDestination) (inst : InstId) (item : Field) (rest : List Field)
    (cursor : Nat) (canonNext : CanonNext grow sig) (right : State grow sig) (canon : Cursor (E := core3 grow) (HostState sig))
    (width : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (atProgram : right.ctl = canon.control (mode.canonical destination inst (item :: rest) cursor >>= canonNext)) :
    Steps profile ready (specDispatch ready (host bindings)) right mode.readLabels
      (focus mode destination inst item cursor right canon
        (canonTail mode destination inst rest (mode.slot destination.width item cursor).2 canonNext)) := by
  cases mode with
  | elements stride =>
    let entered := focus (.elements stride) destination inst item cursor right canon
      (canonTail (.elements stride) destination inst rest (cursor + stride) canonNext)
    have control : right.ctl = entered.ctl := by
      let head : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
        destination.width item (.memory cursor)
      let tail : Session grow sig Unit := CanonicalTree.elements Limits.spec Quirks.none (destination.context inst)
        destination.width rest .value stride (cursor + stride)
      rw [atProgram]
      change canon.control ((head.bind (fun () => tail)).bind canonNext) =
        canon.control (head.bind (fun () => tail.bind canonNext))
      rw [Prog.bind_assoc]
    have same : entered = right :=
      (congrArg (fun ctl => { right with ctl }) control.symm).trans (by cases right; rfl)
    change Steps profile ready (specDispatch ready (host bindings)) right [] entered
    rw [same]
    exact .refl right
  | fields =>
    let cx := destination.context (grow := grow) inst
    let body := fun current =>
      let area := layout current item.type
      let address := alignTo cursor area.alignment
      CanonicalTree.field Limits.spec Quirks.none cx destination.width item (.memory address) >>= fun () =>
        CanonicalTree.memory Limits.spec Quirks.none cx destination.width rest (address + area.size) >>= canonNext
    have atRead : right.ctl = canon.control (ptrType cx >>= body) := by
      rw [atProgram]
      congr 1
      simp only [Track.canonical, CanonicalTree.memory, Prog.bind_eq, Prog.bind_assoc, body, cx]
      congr 1
      funext current
      let area := layout current item.type
      let address := alignTo cursor area.alignment
      let head : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none cx destination.width item (.memory address)
      let tail : Session grow sig Unit := CanonicalTree.memory Limits.spec Quirks.none cx destination.width rest (address + area.size)
      change (head.bind (fun () => tail)).bind canonNext = head.bind (fun () => tail.bind canonNext)
      rw [Prog.bind_assoc]
    have step := (CoreGrowthSteps.refl (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings)) right).read_width
      cx rfl width body atRead
    exact step.steps

theorem replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (compare : FieldComparison grow sig) (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (slots : mode.Slots destination.width (FieldRule compare older origin destination inst) items cursor)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (mode.checked destination inst items index cursor >>= checkNext))
    (canonAt : right.ctl = canon.control (mode.canonical destination inst items cursor >>= canonNext)) :
    Replay profile ready bindings mode destination inst compare checkNext canonNext finish items index cursor left right check canon := by
  induction items generalizing index cursor left right check canon with
  | nil =>
    change finish left right check canon
    apply ends left right check canon frame growth
    · cases mode <;> simpa only [Track.checked, Record.Effects.memory, Record.Effects.elements, Prog.bind_eq, Prog.pure_eq,
        Prog.pure_bind'] using checkAt
    · cases mode <;> simpa only [Track.canonical, CanonicalTree.memory, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq,
        Prog.pure_bind'] using canonAt
  | cons item rest ih =>
    rw [Replay]
    change FieldRule compare older origin destination inst item (mode.slot destination.width item cursor).1 ∧
      mode.Slots destination.width (FieldRule compare older origin destination inst) rest (mode.slot destination.width item cursor).2 at slots
    have width := frame.store ▸ growth.memAddrType present
    refine ⟨focusStep mode destination inst item rest cursor canonNext right canon width canonAt, ?_⟩
    let nextAddress := (mode.slot destination.width item cursor).2
    let nextCheck := checkTail mode destination inst rest (index + 1) nextAddress checkNext
    let nextCanon := canonTail mode destination inst rest nextAddress canonNext
    let focused := focus mode destination inst item cursor right canon nextCanon
    have paired : ChildFrameOver older left focused check canon :=
      ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    refine slots.1 index nextCheck nextCanon left focused check canon paired growth ?_ rfl _ ?_
    · rw [checkAt]
      congr 1
      cases mode <;> simp only [Track.checked, Track.slot, Record.Effects.memory, Record.Effects.elements, Prog.bind_eq, Prog.bind_assoc]
      all_goals
        congr 1
        funext verdict
        cases verdict with
        | error issue => rfl
        | ok result => cases result; rfl
    · intro reached reference pushedCheck pushedCanon paired grown checked canonical
      exact ih (index + 1) (mode.slot destination.width item cursor).2 paired grown slots.2 checked canonical

theorem mixedRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (item : Field) (address : Nat)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    {addr : Nat} (realloc : destination.realloc = some addr) (slot : MixedSlot destination bytes item address) :
    FieldRule (mixed profile ready bindings older destination inst) older origin destination inst item address := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
  rcases slot with handle | ⟨⟨str, rfl, fit⟩, aligned, bounds⟩
  · exact .inl ⟨handle, frame.handle_field_then destination inst item handle index (.memory address) checkNext canonNext
      growth checkAt canonAt (fun () => ends)⟩
  · obtain ⟨reachedBytes, sizeAt, widened⟩ := growth.memSize sized
    change (core3 grow).memSize? left.store.core destination.memory = some reachedBytes at sizeAt
    change address % (layout destination.width (.prim .string : TypeOf)).alignment.bytes = 0 at aligned
    change address + (layout destination.width (.prim .string : TypeOf)).size ≤ bytes at bounds
    have placed : rootPlacement destination left.store (.prim .string) (.memory address) = .ok () := by
      simp [rootPlacement, placement, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans widened)]
      rfl
    exact .inr ⟨str, rfl, frame.string_field_then destination inst str (.memory address) index checkNext canonNext
      growth present realloc fit placed checkAt canonAt (fun () => ends)⟩

theorem aggregateReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (type : TypeOf) (items : List Field) (index address : Nat)
    (compare : FieldComparison grow sig) (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (matched : Field.LayoutMatches (.aggregate type items) type)
    (aligned : address % (layout destination.width type).alignment.bytes = 0)
    (bounds : address + (layout destination.width type).size ≤ bytes)
    (child : ∀ item ∈ items, ∀ slot, SlotFits destination.width bytes item slot → FieldRule compare older origin destination inst item slot)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
      destination.width (.aggregate type items) index (.memory address) >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
      destination.width (.aggregate type items) (.memory address) >>= canonNext)) :
    Steps profile ready (specDispatch ready (host bindings)) left [.tau] (enterAggregate destination inst items index address left check checkNext) ∧
      Replay profile ready bindings .fields destination inst compare (aggregateNext index checkNext) canonNext finish
        items 0 address (enterAggregate destination inst items index address left check checkNext) right check canon := by
  let area := layout destination.width type
  let body := Track.fields.checked (grow := grow) (sig := sig) destination inst items 0 address >>= aggregateNext index checkNext
  obtain ⟨reachedBytes, sizeAt, widened⟩ := growth.memSize sized
  change (core3 grow).memSize? left.store.core destination.memory = some reachedBytes at sizeAt
  have placementAt : placement destination left.store area address = .ok () := by
    simp [placement, area, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans widened)]
    rfl
  have guardAt : left.ctl = check.control (do
      checkAligned address area.alignment.bytes
      checkInBounds (destination.context inst) address area.size
      body) := by
    rw [Record.Effects.field] at checkAt
    let children := Track.fields.checked (grow := grow) (sig := sig) destination inst items 0 address
    let range : Session grow sig Unit := checkInBounds (destination.context inst) address area.size
    change left.ctl = check.control ((range.bind fun () => children.bind fun verdict =>
      Prog.pure (verdict.mapError (.nested index))).bind checkNext) at checkAt
    rw [Prog.bind_assoc] at checkAt
    have focused : left.ctl = check.control (range.bind fun () => body) := by
      rw [checkAt]
      congr 2
      funext result
      cases result
      simp only [Prog.bind_assoc, Prog.pure_bind']
      rfl
    simpa [checkAligned, trapIf, area, aligned, Prog.bind_eq, Prog.pure_bind', range] using focused
  have guard := check_placement_steps (profile := profile) (placementReady := ready) (placementDispatch := specDispatch ready (host bindings))
    destination inst left area address check body guardAt
  rw [placementAt] at guard
  rw [CanonicalTree.field] at canonAt
  refine ⟨guard, replay .fields destination inst items 0 address compare (aggregateNext index checkNext) canonNext finish ?_
    growth present (aggregateSlots destination.width matched aligned bounds _ child) ends rfl canonAt⟩
  exact ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩

private theorem matchedField {items : List Field} {types : List TypeOf} {item : Field}
    (matched : Field.FieldsMatch items types) (member : item ∈ items) : item.LayoutMatches item.type := by
  induction items generalizing types with
  | nil => simp at member
  | cons first rest ih =>
    cases matched with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | inside
      · rw [head.type_eq]; exact head
      · exact ih tail inside

private theorem matchedAggregateChild {children : List Field} {type : TypeOf} {child : Field}
    (matched : Field.LayoutMatches (.aggregate type children) type) (member : child ∈ children) : child.LayoutMatches child.type := by
  cases matched with
  | record childMatches => exact matchedField childMatches member
  | tuple childMatches => exact matchedField childMatches member

theorem nestedRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (depth : Nat) (item : Field) (address : Nat)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (shape : AggregateShape (StringField.Fits destination) depth item) (matched : item.LayoutMatches item.type)
    (placement : SlotFits destination.width bytes item address) :
    FieldRule (nested profile ready bindings older destination inst depth) older origin destination inst item address := by
  induction depth generalizing item address with
  | zero =>
    cases shape with
    | handle handle => exact mixedRule destination inst item address present sized realloc (.inl handle)
    | string fit => exact mixedRule destination inst item address present sized realloc (.inr ⟨fit, placement⟩)
  | succ depth ih =>
    intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
    cases shape with
    | handle handle => exact .inl (mixedRule destination inst item address present sized realloc (.inl handle)
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends)
    | string fit => exact .inl (mixedRule destination inst item address present sized realloc (.inr ⟨fit, placement⟩)
        index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends)
    | @aggregate _ type children child =>
      refine .inr ⟨type, children, rfl, aggregateReplay destination inst type children index address _
        checkNext canonNext finish frame growth present sized matched placement.1 placement.2 ?_ ends checkAt canonAt⟩
      exact fun entry member slot fits => ih entry slot (child entry member) (matchedAggregateChild matched member) fits

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence
