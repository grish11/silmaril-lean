module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Component.Reference.ABI.Layout.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.NestedRecord

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem appendSteps {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start middle finish : State grow sig} {first second : List (Label (core3 grow) (HostState sig))}
    (leading : Steps profile ready dispatch start first middle) (trailing : Steps profile ready dispatch middle second finish) :
    Steps profile ready dispatch start (first ++ second) finish := by
  induction leading with
  | refl => exact trailing
  | cons step _ next => exact .cons step (next trailing)

private theorem widthOf (site : Site) {origin store : CStore (core3 grow)} {bytes : Nat}
    (region : site.Region origin bytes) (growth : Core3.Grows origin.core store.core) :
    ptrTypeIn store (site.destination.context site.inst) = site.destination.width := by
  have reached : (core3 grow).memAddrType? store.core site.destination.memory = some site.destination.width :=
    growth.memAddrType region.width
  simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, reached]

private theorem suffix (site : Site) {origin : CStore (core3 grow)} {bytes : Nat} (region : site.Region origin bytes)
    (child : ∀ item ∈ site.following, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item item.type)
    (left right : State grow sig) (growth : Core3.Grows origin.core right.store.core) :
    CompareKeepingAt profile ready (specDispatch ready (host (grow := grow) bindings))
      (fun store => Core3.Grows origin.core store.core) left right site.checkedTail site.canonicalTail := by
  let layouts := site.fields.map fun item => layout site.destination.width item.type
  have layoutEq : layout site.destination.width site.schema = recordLayout layouts :=
    compiled_aggregate_layout site.destination.width region.layoutMatch
  have aligned := region.aligned
  have bounds := region.fits
  rw [layoutEq] at aligned bounds
  apply memory_fields_at site.destination site.inst site.following site.advance (site.index + 1)
    (fun _ grown => widthOf site region grown) _ left right growth
  intro slot item address found placed checked canonical grown
  have member : layouts[slot + 1]? = some (layout site.destination.width item.type) := by
    simp only [layouts, Site.fields, List.map_cons, List.getElem?_cons_succ, List.getElem?_map, found, Option.map_some]
  have offset : (fieldOffsets site.base layouts)[slot + 1]? = some address := by
    simpa only [layouts, Site.fields, List.map_cons, fieldOffsets, List.getElem?_cons_succ, placeField,
      Site.advance, Site.address, Site.headLayout] using placed
  obtain ⟨_, addressAligned, fits⟩ := recordLayout_field_fits layouts site.base (slot + 1) address _ aligned member offset
  exact child item (List.mem_of_getElem? found) origin (site.index + 1 + slot) address bytes
    region.width region.sized addressAligned (fits.trans bounds) checked canonical grown

theorem atCursor (site : Site) {origin : CStore (core3 grow)} {bytes : Nat} (region : site.Region origin bytes)
    (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig)
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (growth : Core3.Grows origin.core right.store.core)
    (children : ∀ item ∈ site.entries, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item site.element)
    (following : ∀ item ∈ site.following, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item item.type)
    (checkAt : left.ctl = cursor.control (Record.Effects.memory recordClaims Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width site.fields site.base site.index >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.memory Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width site.fields site.base >>= canonNext)) :
    site.Outcome profile ready bindings origin left right cursor checkNext canonNext := by
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  let cx := site.destination.context (grow := grow) site.inst
  let keep := fun (store : CStore (core3 grow)) => Core3.Grows origin.core store.core
  let checkHeadNext := checkedSequenceNext id (fun _ : Unit => site.checkedTail) checkNext
  let canonHeadNext := fun _ : Unit => site.canonicalTail >>= canonNext
  have checkHead : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx
      site.destination.width site.head site.index (.memory site.address) >>= checkHeadNext) := by
    rw [Site.fields, Record.Effects.memory] at checkAt
    simp only [Prog.bind_eq, Prog.bind_assoc] at checkAt ⊢
    convert checkAt using 4
    change Prog.bind (Record.Effects.field recordClaims Limits.spec Quirks.none cx site.destination.width
      site.head site.index (.memory site.address)) checkHeadNext = _
    apply congrArg (Prog.bind (Record.Effects.field recordClaims Limits.spec Quirks.none cx
      site.destination.width site.head site.index (.memory site.address)))
    funext verdict
    cases verdict with
    | ok value => cases value; rfl
    | error _ => rfl
  have later (_ : Unit) (entered reference : State grow sig) (grown : keep reference.store) :
      CompareKeepingAt profile ready dispatch keep entered reference site.checkedTail site.canonicalTail :=
    suffix site region following entered reference grown
  unfold Site.Outcome
  cases prepared : Record.prepare left.store left.host.writer (Field.listObjects site.entries) with
  | error issue =>
    have sameStore : left.store = right.store := by
      simpa only using congrArg (fun (cfg : State grow sig) => cfg.store) same
    have stopped := dynamic_refused_before_allocation (profile := profile) (ready := ready) (dispatch := dispatch)
      site.destination site.inst (.list site.element) site.element site.entries (.memory site.address) site.index
      left right cursor cursor checkHeadNext canonHeadNext sameStore issue prepared checkHead (keep := keep)
    exact ReachesKeeping.bind_reached rfl id (fun _ : Unit => site.checkedTail) (fun _ => site.canonicalTail) stopped later
  | ok passed =>
    cases passed
    dsimp only
    let canonBody : AddrType → Session grow sig Unit := fun width => do
      let area := layout width site.head.type
      let address := alignTo site.base area.alignment
      CanonicalTree.field Limits.spec Quirks.none cx site.destination.width site.head (.memory address)
      CanonicalTree.memory Limits.spec Quirks.none cx site.destination.width site.following (address + area.size)
    have readAt : right.ctl = cursor.control (ptrType cx >>= fun width => canonBody width >>= canonNext) := by
      rw [Site.fields, CanonicalTree.memory] at canonAt
      simpa only [cx, canonBody, Prog.bind_eq, Prog.bind_assoc] using canonAt
    let entered := { right with ctl := cursor.control (canonBody site.destination.width >>= canonNext) }
    have read : Step profile ready dispatch right .tau entered := by
      have step := Step.get (prof := profile) (hr := ready) (dispatch := dispatch)
        (k := fun store => canonBody (ptrTypeIn store cx) >>= canonNext) readAt
      have width : ptrTypeIn right.store cx = site.destination.width := widthOf site region growth
      simpa only [entered, Cursor.control, width] using step
    have sameEntered : { left with ctl := entered.ctl, host := entered.host } = entered :=
      congrArg (fun cfg : State grow sig => { cfg with ctl := entered.ctl }) same
    have canonHead : entered.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none cx
        site.destination.width site.head (.memory site.address) >>= canonHeadNext) := by
      change cursor.control (((CanonicalTree.field Limits.spec Quirks.none cx site.destination.width site.head
        (.memory site.address)).bind (fun _ => site.canonicalTail)).bind canonNext) = _
      rw [Prog.bind_assoc]
      rfl
    constructor
    · intro last seen path
      have reachedWidth := growth.memAddrType region.width
      obtain ⟨checkedInstall, canonicalInstall, paired⟩ := collection_install
        site.destination site.inst (.list site.element) site.element site.entries (.memory site.address) site.index
        left entered cursor checkHeadNext canonHeadNext sameEntered reachedWidth rfl prepared checkHead canonHead
      obtain ⟨checkedLabels, canonicalLabels, other, checkedRun, canonicalRun, related, checkedSeen, canonicalSeen⟩ :=
        path.replay paired
      have sameStore : left.store = right.store := by
        simpa only using congrArg (fun cfg : State grow sig => cfg.store) same
      have grown : keep last.store := (sameStore ▸ growth).trans checkedRun.grows
      exact ⟨_, _, other, appendSteps checkedInstall checkedRun.steps, .cons read (appendSteps canonicalInstall canonicalRun.steps),
        related, checkedSeen, canonicalSeen, grown⟩
    intro pointer last seen reached path returned
    have cut := Prefix.collection_memory site.destination site.inst (.list site.element) site.element site.entries
      (.memory site.address) site.index pointer cursor reached checkHeadNext canonHeadNext
      sameEntered growth region.width region.sized rfl prepared checkHead canonHead path returned children
    rcases cut with ⟨referenceCursor, thread, done⟩ | common
    · have continued := ReachesKeeping.bind_reached thread.symm id (fun _ : Unit => site.checkedTail)
        (fun _ => site.canonicalTail) done later
      exact .inl ⟨referenceCursor, thread, continued.prepend (.refl _) (.cons read (.refl _)) rfl⟩
    · obtain ⟨checkLabels, canonLabels, other, checks, canonical, paired, checkSeen, canonSeen⟩ := common
      exact .inr ⟨checkLabels, .tau :: canonLabels, other, checks, .cons read canonical, paired, checkSeen, canonSeen⟩

private theorem tailLayout {fields : List Field} {types : List TypeOf} (matched : Field.FieldsMatch fields types)
    {item : Field} (member : item ∈ fields) : item.LayoutMatches item.type := by
  induction fields generalizing types with
  | nil => simp at member
  | cons _ _ ih =>
    cases matched with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | member
      · rw [head.type_eq]
        exact head
      · exact ih tail member

private theorem listAndTail {schema element : TypeOf} {entries following : List Field}
    (matched : Field.LayoutMatches (.aggregate schema (.dynamic (.list element) element entries :: following)) schema) :
    Field.EntriesMatch entries element ∧ ∀ item ∈ following, item.LayoutMatches item.type := by
  have both {types : List TypeOf}
      (fields : Field.FieldsMatch (.dynamic (.list element) element entries :: following) types) :
      Field.EntriesMatch entries element ∧ ∀ item ∈ following, item.LayoutMatches item.type := by
    cases fields with
    | cons head tail =>
      refine ⟨?_, fun _ member => tailLayout tail member⟩
      cases head with
      | list entries => exact entries
  cases matched with
  | record fields => exact both fields
  | tuple fields => exact both fields

private theorem placedRegion (site : Site) (start : CStore (core3 grow))
    (matched : Field.LayoutMatches (.aggregate site.schema site.fields) site.schema)
    (width : (core3 grow).memAddrType? start.core site.destination.memory = some site.destination.width)
    (placed : placement site.destination start (layout site.destination.width site.schema) site.base = .ok ()) :
    ∃ bytes, site.Region start bytes := by
  by_cases aligned : site.base % (layout site.destination.width site.schema).alignment.bytes = 0
  · cases sized : (core3 grow).memSize? start.core site.destination.memory with
    | none => simp [placement, aligned, sized] at placed
    | some bytes =>
      by_cases fits : site.base + (layout site.destination.width site.schema).size ≤ bytes
      · exact ⟨bytes, matched, width, sized, Nat.dvd_of_mod_eq_zero aligned, fits⟩
      · simp [placement, aligned, sized, Nat.lt_of_not_ge fits] at placed
  · simp [placement, aligned] at placed
    cases placed

theorem parked {pointer : FlatValue} (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (element : TypeOf) (entries following : List Field) (next : call.ReferenceNext)
    (field : call.field = .aggregate (sig.payload call.tag) (.dynamic (.list element) element entries :: following))
    (localEntries : ∀ item ∈ entries, LocalMemory item) (localTail : ∀ item ∈ following, LocalMemory item) :
    PublicOutcome call element entries following next profile ready bindings := by
  let site := publicSite call element entries following
  rcases call.parked (profile := profile) (ready := ready) linked with
    ⟨issue, silent, stopped⟩ | ⟨reason, count, placed, halted⟩ | ⟨silent, placed, prepared, run, _⟩
  · exact .refused issue silent stopped
  · exact .placementTrap reason count placed halted
  · obtain ⟨plan, compiled⟩ := linked.compiled
    have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
    rw [field] at matched
    have width := call.destination.check_width call.start.store linked.destination
    obtain ⟨bytes, region⟩ := placedRegion site call.start.store matched width placed
    obtain ⟨childMatch, tailMatch⟩ := listAndTail matched
    let area := layout call.destination.width (sig.payload call.tag)
    have checked : call.checked.ctl = call.cursor.control (do
        checkAligned (flatNat pointer) area.alignment.bytes
        checkInBounds (call.destination.context call.inst) (flatNat pointer) area.size
        publicBody call site) := by
      change call.cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none (call.destination.context call.inst)
        call.destination.width call.field 0 (.memory (flatNat pointer)) >>= call.reply) = _
      have aligned : flatNat pointer % area.alignment.bytes = 0 := Nat.mod_eq_zero_of_dvd region.aligned
      simp [field, Record.Effects.field, site, publicSite, Site.fields, Site.head, checkAligned, trapIf, aligned, area,
        publicBody, Prog.bind_eq, Prog.pure_bind']
      let read : Session grow sig Unit := checkInBounds (call.destination.context call.inst) (flatNat pointer) area.size
      let body : Session grow sig (Except RecordLower.Issue Unit) :=
        Record.Effects.memory recordClaims Limits.spec Quirks.none (site.destination.context site.inst)
        site.destination.width site.fields site.base site.index
      let finish : CheckNext grow sig := call.reply
      change call.cursor.control ((read.bind fun _ => body.bind fun verdict => .pure (verdict.mapError (.nested 0))).bind finish) =
        call.cursor.control (read.bind fun _ => body.bind (publicReply call))
      simp only [Prog.bind_assoc, Prog.pure_bind']
      rfl
    have bounds := check_placement_steps (profile := profile) (placementReady := ready)
      (placementDispatch := specDispatch ready (host (grow := grow) bindings))
      call.destination call.inst call.checked area (flatNat pointer) call.cursor (publicBody call site) checked
    have placedHere : placement call.destination call.checked.store area (flatNat pointer) = .ok () := placed
    rw [placedHere] at bounds
    have reference : (call.reference next).ctl = call.cursor.control (CanonicalTree.memory Limits.spec Quirks.none
        (site.destination.context site.inst) site.destination.width site.fields site.base >>= next) := by
      rw [call.reference_at linked next]
      change call.cursor.control (CanonicalTree.field Limits.spec Quirks.none (call.destination.context call.inst)
        call.destination.width call.field (.memory (flatNat pointer)) >>= next) = _
      simp only [field, CanonicalTree.field, site, publicSite, Site.fields, Site.head]
      rfl
    exact .placed silent placed prepared run ⟨bounds, atCursor site region (call.withBody (publicBody call site))
      (call.reference next) call.cursor (publicReply call) next rfl (Core3.Grows.refl _) (fun item member => MemoryChildRule.local_memory site.destination site.inst
        (localEntries item member) (entries_match_of_mem childMatch member))
      (fun item member => MemoryChildRule.local_memory site.destination site.inst (localTail item member) (tailMatch item member))
      rfl reference⟩

theorem flatAtCursor (site : FlatSite) {origin : CStore (core3 grow)} {bytes : Nat}
    (width : (core3 grow).memAddrType? origin.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? origin.core site.destination.memory = some bytes)
    (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : FlatCheckNext grow sig) (canonNext : FlatCanonNext grow sig)
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (growth : Core3.Grows origin.core right.store.core)
    (children : ∀ item ∈ site.entries, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item site.element)
    (following : HandleFieldsWhere Nat.lt site.following)
    (checkAt : left.ctl = cursor.control (site.checked >>= checkNext))
    (canonAt : right.ctl = cursor.control (site.canonical >>= canonNext)) :
    site.Outcome profile ready bindings origin left right cursor checkNext canonNext := by
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  let cx := site.destination.context (grow := grow) site.inst
  let type : TypeOf := .list site.element
  let head : Field := .dynamic type site.element site.entries
  let checkHeadNext := checkedSequenceNext id site.checkedTail checkNext
  let canonHeadNext : FlatCanonNext grow sig := fun words => site.canonicalTail words >>= canonNext
  let checkField : Session grow sig (Except RecordLower.Issue (List FlatValue)) :=
    Record.Effects.field recordClaims Limits.spec Quirks.none cx site.destination.width head site.index .flat
  let canonField : Session grow sig (List FlatValue) :=
    CanonicalTree.field Limits.spec Quirks.none cx site.destination.width head .flat
  have checkHead : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx
      site.destination.width head site.index .flat >>= checkHeadNext) := by
    rw [FlatSite.checked, FlatSite.fields, Record.Effects.flat] at checkAt
    simp only [Lower.Output.Result] at checkAt
    rw [checkAt]
    change cursor.control ((checkField.bind _).bind checkNext) = cursor.control (checkField.bind checkHeadNext)
    rw [Prog.bind_assoc]
    apply congrArg (fun finish => cursor.control (checkField.bind finish))
    funext verdict
    cases verdict <;> rfl
  have canonHead : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none cx
      site.destination.width head .flat >>= canonHeadNext) := by
    rw [FlatSite.canonical, FlatSite.fields, CanonicalTree.flat] at canonAt
    rw [canonAt]
    change cursor.control ((canonField.bind site.canonicalTail).bind canonNext) =
      cursor.control (canonField.bind canonHeadNext)
    rw [Prog.bind_assoc]
    rfl
  have later (words : List FlatValue) (entered reference : State grow sig) :
      CompareKeepingAt profile ready dispatch (fun _ => True) entered reference
        (site.checkedTail words) (site.canonicalTail words) := by
    intro stores checkCursor canonCursor thread checkFinish canonFinish checked canonical
    exact (flat_fields_prepend site.destination site.inst site.following following (site.index + 1) words
      entered reference stores checkCursor canonCursor thread checkFinish canonFinish checked canonical).remember_true
  have sameStore : left.store = right.store := by
    simpa only using congrArg (fun cfg : State grow sig => cfg.store) same
  unfold FlatSite.Outcome
  cases prepared : Record.prepare left.store left.host.writer (Field.listObjects site.entries) with
  | error issue =>
    have stopped := dynamic_refused_before_allocation (profile := profile) (ready := ready) (dispatch := dispatch)
      site.destination site.inst type site.element site.entries .flat site.index left right cursor cursor
      checkHeadNext canonHeadNext sameStore issue prepared checkHead (keep := fun _ => True)
    exact (stopped.bind_reached rfl id site.checkedTail site.canonicalTail (fun words entered reference _ =>
      later words entered reference)).forget
  | ok passed =>
    cases passed
    constructor
    · intro last seen path
      obtain ⟨checkedInstall, canonicalInstall, paired⟩ := collection_install
        site.destination site.inst type site.element site.entries .flat site.index left right cursor checkHeadNext
        canonHeadNext same (growth.memAddrType width) rfl prepared checkHead canonHead
      obtain ⟨_, _, other, checkedRun, canonicalRun, related, checkedSeen, canonicalSeen⟩ := path.replay paired
      exact ⟨_, _, other, appendSteps checkedInstall checkedRun.steps, appendSteps canonicalInstall canonicalRun.steps,
        related, checkedSeen, canonicalSeen, (sameStore ▸ growth).trans checkedRun.grows⟩
    intro pointer last seen reached path returned
    have cut := Prefix.collection_memory site.destination site.inst type site.element site.entries .flat site.index
      pointer cursor reached checkHeadNext canonHeadNext same growth width sized rfl prepared checkHead canonHead
      path returned children
    rcases cut with ⟨referenceCursor, thread, done⟩ | common
    · have localDone := done.weaken (weaker := fun _ => True) (fun _ _ => trivial)
      exact .inl ⟨referenceCursor, thread, (localDone.bind_reached thread.symm id site.checkedTail site.canonicalTail
        (fun words entered reference _ => later words entered reference)).forget⟩
    · exact .inr common

theorem parkedFlat {schema : TypeOf} (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (element : TypeOf) (entries following : List Field) (next : call.ReferenceNext)
    (field : call.field = .aggregate (sig.payload call.tag) (.dynamic (.list element) element entries :: following))
    (localEntries : ∀ item ∈ entries, LocalMemory item) (localTail : ∀ item ∈ following, HandleShape item) :
    PublicFlatOutcome call element entries following next profile ready bindings := by
  let site := publicFlatSite call element entries following
  rcases call.parked (profile := profile) (ready := ready) linked with
    ⟨issue, silent, stopped⟩ | ⟨reason, count, placed, halted⟩ | ⟨silent, placed, prepared, run, _⟩
  · exact .refused issue silent stopped
  · exact .placementTrap reason count placed halted
  · obtain ⟨plan, compiled⟩ := linked.compiled
    have matched := Record.preflightValue_layout _ _ _ _ _ plan compiled
    rw [field] at matched
    obtain ⟨childMatch, tailMatch⟩ := listAndTail matched
    have tail : HandleFieldsWhere Nat.lt following := by
      suffices ∀ items : List Field, (∀ item ∈ items, HandleField item) → HandleFieldsWhere Nat.lt items from
        this following fun item member => checked_fragment (tailMatch item member) (localTail item member)
      intro items
      induction items with
      | nil => exact fun _ => trivial
      | cons item rest ih =>
        intro each
        exact ⟨each item (List.mem_cons_self ..), ih fun child member => each child (List.mem_cons_of_mem _ member)⟩
    have checked : call.checked.ctl = call.cursor.control (site.checked >>= publicFlatReply call) := by
      change call.cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none (call.destination.context call.inst)
        call.destination.width call.field 0 .flat >>= call.reply) = _
      rw [field, Record.Effects.field]
      let finish : FlatCheckNext grow sig := call.reply
      change call.cursor.control ((site.checked.bind fun verdict => .pure (verdict.mapError (.nested 0))).bind finish) =
        call.cursor.control (site.checked.bind (publicFlatReply call))
      simp only [Prog.bind_assoc, Prog.pure_bind']
      rfl
    have reference : (call.reference next).ctl = call.cursor.control (site.canonical >>= next) := by
      rw [call.reference_at linked next]
      change call.cursor.control (CanonicalTree.field Limits.spec Quirks.none (call.destination.context call.inst)
        call.destination.width call.field .flat >>= next) = _
      rw [field, CanonicalTree.field]
      rfl
    have width := call.destination.check_width call.start.store linked.destination
    have sizePresent := (Silmaril.Wasm.Component.Engine.Core3.memAddrType?_isSome_iff
      (s := call.start.store.core) (m := call.destination.memory)).mp
      (show ((core3 grow).memAddrType? call.start.store.core call.destination.memory).isSome by simp [width])
    obtain ⟨bytes, sized⟩ := Option.isSome_iff_exists.mp sizePresent
    exact .placed silent placed prepared run (flatAtCursor site width sized call.checked (call.reference next) call.cursor
      (publicFlatReply call) next rfl (Core3.Grows.refl _) (fun item member => MemoryChildRule.local_memory
        site.destination site.inst (localEntries item member) (entries_match_of_mem childMatch member)) tail checked reference)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.NestedRecord
