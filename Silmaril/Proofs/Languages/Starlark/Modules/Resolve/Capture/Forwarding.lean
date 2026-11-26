module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
public import Mathlib.Data.List.Chain

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding

open Silmaril.Languages.Starlark (Binding Scope)
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment
open Silmaril.Languages.Starlark.Modules.Resolve.Block
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Functions (Program FreeName Signature activate capturedSlots captureName)
open Silmaril.Languages.Starlark.Lists (State Address Value)
open Silmaril.Languages.Starlark.Functions.Comprehensions (assignPatternCode directStages)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve
  (Context resolveTracked resolveExpr resolveScalar resolveRead resolveReadValue)

theorem nearest_iff (name : String) (outer : List (List String)) :
    name ∈ outer.flatten ↔ ∃ distance, Nearest name outer distance := by
  induction outer with
  | nil =>
    constructor
    · intro missing; cases missing
    · rintro ⟨_, nearest⟩; cases nearest
  | cons owned outer ih =>
    rw [List.flatten_cons, List.mem_append, ih]
    constructor
    · intro present
      by_cases here : name ∈ owned
      · exact ⟨0, .owns here⟩
      · obtain ⟨distance, there⟩ := present.resolve_left here
        exact ⟨distance + 1, .farther here there⟩
    · rintro ⟨_, nearest⟩
      cases nearest with
      | owns here => exact .inl here
      | farther _ there => exact .inr ⟨_, there⟩

private theorem selected_member {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selected : Selects block reads free) (binding : Binding) :
    reference binding ∈ free ↔ binding ∈ reads ∧ (binding.scope = .global ∨ binding.name ∉ block.owned) := by
  rw [← captureNames_eq selected, captureNames, List.mem_map]
  constructor
  · rintro ⟨seen, present, equal⟩
    have same : seen = binding := congrArg FreeName.source equal
    subst seen
    simpa using List.mem_filter.mp present
  · intro member
    exact ⟨binding, List.mem_filter.mpr (by simpa using member), rfl⟩

private theorem selected_origin {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selected : Selects block reads free) (entry : FreeName) (present : entry ∈ free) :
    ∃ binding, entry = reference binding ∧
      (ReadOrigin block binding .enclosing ∨ ReadOrigin block binding .module) := by
  induction selected with
  | nil => cases present
  | owned _ _ ih => exact ih present
  | enclosing origin _ ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨_, rfl, .inl origin⟩
    · exact ih present
  | module origin _ ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨_, rfl, .inr origin⟩
    · exact ih present

private theorem head_selection {globals : List String} {outer : List (List String)}
    {chain : Chain} {head : Frame} {rest : List Frame}
    (emitted : Emits globals outer chain (head :: rest)) :
    ∃ reads, Selects ⟨head.owned, outer.flatten, globals⟩ reads head.free := by
  cases emitted with
  | mixed _ _ selected => exact ⟨_, selected⟩
  | wrapper _ _ selected => exact ⟨_, selected⟩

theorem root_capture {globals : List String} {chain : Chain} {head : Frame} {rest : List Frame}
    (emitted : Emits globals [] chain (head :: rest)) (entry : FreeName) (present : entry ∈ head.free) :
    ∃ name ∈ globals, entry = reference (globalSlot name) := by
  obtain ⟨_, selected⟩ := head_selection emitted
  obtain ⟨binding, same, origin⟩ := selected_origin selected entry present
  rcases origin with enclosing | global
  · cases enclosing with
    | enclosing _ missing => cases missing
  · cases global with
    | module _ _ member => exact ⟨_, member, same⟩

private theorem child_read_origin (parameters locals : List String)
    {globals : List String} {outer : List (List String)} {child : Chain} {head : Frame} {rest : List Frame}
    (emitted : Emits globals ((parameters ++ locals) :: outer) child (head :: rest))
    (entry : FreeName) (present : entry ∈ head.free) :
    ∃ origin, ReadOrigin ⟨parameters ++ locals, outer.flatten, globals⟩ entry.source origin := by
  obtain ⟨_, selected⟩ := head_selection emitted
  obtain ⟨binding, rfl, classified⟩ := selected_origin selected entry present
  rcases classified with enclosing | global
  · cases enclosing with
    | @enclosing name _ found =>
      by_cases owns : name ∈ parameters ++ locals
      · exact ⟨_, .owned owns⟩
      · exact ⟨_, .enclosing owns ((List.mem_append.mp found).resolve_left owns)⟩
  · cases global with
    | module _ absent member =>
      exact ⟨_, .module (fun h => absent (List.mem_append_left _ h))
        (fun h => absent (List.mem_append_right _ h)) member⟩

private theorem wrapper_owns_child (parameters locals : List String) (name : String)
    (declared : LocalBinders parameters [name] locals) : name ∈ parameters ++ locals := by
  cases declared with
  | skip member _ => exact List.mem_append_left _ member
  | keep _ _ => exact List.mem_append_right _ List.mem_cons_self

private theorem tracked_local (context : Context) (name : String)
    (legal : name.toList.head? ≠ some '$') (member : name ∈ context.locals) :
    resolveTracked context (.scalar (.read name)) =
      .ok (.atom (.read (.bound (fileSlot name))), [fileSlot name]) := by
  rw [resolveTracked, resolveExpr.eq_def]
  simp [resolveScalar, resolveRead, resolveReadValue, Silmaril.Languages.Starlark.resolveName, legal, member,
    fileSlot, Except.map]

theorem compile_chain_scoped {globals : List String} {program : Program}
    {outer : List (List String)} {chain : Chain} (accepted : Accepted globals program outer chain) :
    ∃ head rest, Emits globals outer chain (head :: rest) ∧ Links program chain (head :: rest) ∧
      ScopedLeaves globals outer chain (head :: rest) ∧
      compileBody (parentContext globals outer) chain.definition program =
        .ok (⟨.define (fileSlot chain.name) (EmittedProgram program rest).size, head.free.map FreeName.source⟩,
          EmittedProgram program (head :: rest)) := by
  induction accepted with
  | @mixed outer name parameters locals body next assignment returned returnReads
      localDecls targetProfile rhsProfile returnProfile assigned resolvedReturn =>
    obtain ⟨free, leaf, reads, selected, compiled⟩ := mixed_definition_linked (parentContext globals outer) name parameters locals
      body localDecls targetProfile rhsProfile returnProfile program next assignment returned returnReads
      assigned resolvedReturn
    let frame : Frame := ⟨parameters, locals, free,
      .seq (assignPatternCode assignment.pattern assignment.rhs directStages) (.returnExpr returned)⟩
    exact ⟨frame, [], .mixed localDecls reads selected, .mixed _ _ _ _ _ leaf, .mixed leaf, compiled⟩
  | @wrapper outer name parameters locals child localDecls legal childAccepted ih =>
    obtain ⟨head, rest, emitted, linked, scopes, compiledChild⟩ := ih
    have named := wrapper_owns_child parameters locals child.name localDecls
    let block : LexicalBlock := ⟨parameters ++ locals, outer.flatten, globals⟩
    let reads := head.free.map FreeName.source ++ [fileSlot child.name]
    have origins : ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin := by
      intro binding present
      rcases List.mem_append.mp present with fromChild | fromReturn
      · obtain ⟨entry, member, rfl⟩ := List.mem_map.mp fromChild
        exact child_read_origin parameters locals emitted entry member
      · cases List.mem_singleton.mp fromReturn
        exact ⟨_, .owned named⟩
    obtain ⟨free, selected⟩ := selects_of_origins block origins
    let context := parentContext globals ((parameters ++ locals) :: outer)
    have layout : collectFunctionLayout (parentContext globals outer).reads (.required parameters)
        (.wrapper name parameters child : Chain).body = .ok ⟨locals, context⟩ := by
      exact collectFunctionLayout_eq _ (required_parameter_binders parameters) (.seq (.define _ _ _) (.ret _))
        localDecls
    have returnResolved := tracked_local context.reads child.name legal (List.mem_append_left _ named)
    have compiledBody := compileBody_seqReturn context child.definition (.scalar (.read child.name)) program
      (EmittedProgram program (head :: rest)) _ _ _ compiledChild returnResolved
    have compiled := compileBody_requiredDefinition (parentContext globals outer) name parameters
      (.wrapper name parameters child : Chain).body program (EmittedProgram program (head :: rest))
      ⟨locals, context⟩ _ layout compiledBody
    have exactFree := captureNames_eq selected
    let frame : Frame := ⟨parameters, locals, free, .seq
      (.define (fileSlot child.name) (EmittedProgram program rest).size)
      (.returnExpr (.atom (.read (.bound (fileSlot child.name)))))⟩
    refine ⟨frame, head :: rest, .wrapper localDecls emitted selected, .wrapper named rfl linked, .wrapper scopes, ?_⟩
    change captureNames (parameters ++ locals) (head.free.map FreeName.source ++ [fileSlot child.name]) =
      free at exactFree
    dsimp only at compiled
    rw [exactFree] at compiled
    exact compiled

theorem compile_chain_linked {globals : List String} {program : Program}
    {outer : List (List String)} {chain : Chain} (accepted : Accepted globals program outer chain) :
    ∃ head rest, Emits globals outer chain (head :: rest) ∧ Links program chain (head :: rest) ∧
      compileBody (parentContext globals outer) chain.definition program =
        .ok (⟨.define (fileSlot chain.name) (EmittedProgram program rest).size, head.free.map FreeName.source⟩,
          EmittedProgram program (head :: rest)) := by
  obtain ⟨head, rest, emitted, linked, _, compiled⟩ := compile_chain_scoped accepted
  exact ⟨head, rest, emitted, linked, compiled⟩

theorem compile_chain {globals : List String} {program : Program}
    {outer : List (List String)} {chain : Chain} (accepted : Accepted globals program outer chain) :
    ∃ head rest, Emits globals outer chain (head :: rest) ∧
      compileBody (parentContext globals outer) chain.definition program =
        .ok (⟨.define (fileSlot chain.name) (EmittedProgram program rest).size, head.free.map FreeName.source⟩,
          EmittedProgram program (head :: rest)) := by
  obtain ⟨head, rest, emitted, _, compiled⟩ := compile_chain_linked accepted
  exact ⟨head, rest, emitted, compiled⟩

theorem emitted_declaration (program : Program) (frames : List Frame) (frame : Frame)
    (present : frame ∈ frames) : ∃ id : Nat, (EmittedProgram program frames)[id]? = some frame.declaration := by
  induction frames with
  | nil => cases present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨(EmittedProgram program rest).size, Array.getElem?_push_size⟩
    · obtain ⟨id, found⟩ := ih present
      have within := (Array.getElem?_eq_some_iff.mp found).choose
      exact ⟨id, by simp [EmittedProgram, Array.getElem?_push, Nat.ne_of_lt within, found]⟩

private theorem scoped_selection (frame : Frame) (outer globals : List String) {reads : List Binding}
    (selected : Selects ⟨frame.owned, outer, globals⟩ reads frame.free) : frame.WellScoped := by
  intro entry present
  obtain ⟨binding, equal, origin⟩ := selected_origin selected entry present
  refine ⟨binding, equal, ?_⟩
  rcases origin with enclosing | global
  · cases enclosing with
    | enclosing absent _ => exact .inr absent
  · cases global
    exact .inl rfl

theorem scoped_frames {globals : List String} {outer : List (List String)} {chain : Chain}
    {frames : List Frame} (emitted : Emits globals outer chain frames) :
    ∀ frame ∈ frames, frame.WellScoped := by
  induction emitted with
  | mixed _ _ selected =>
    intro frame present
    cases List.mem_singleton.mp present
    exact scoped_selection _ _ _ selected
  | wrapper _ _ selected ih =>
    intro frame present
    rcases List.mem_cons.mp present with rfl | present
    · exact scoped_selection _ _ _ selected
    · exact ih frame present

private theorem out_of_owned {globals : List String} {outer : List (List String)}
    {chain : Chain} {frames : List Frame} (emitted : Emits globals outer chain frames)
    (frame : Frame) (present : frame ∈ frames) (name : String) (owned : name ∈ frame.owned) :
    reference (fileSlot name) ∉ frame.free := by
  intro captured
  obtain ⟨binding, sameReference, external⟩ := scoped_frames emitted frame present _ captured
  have equal : fileSlot name = binding := congrArg FreeName.source sameReference
  subst binding
  exact external.elim (by simp [fileSlot]) (fun absent => absent owned)

theorem passes_along {globals : List String} {outer : List (List String)}
    {chain : Chain} {frames : List Frame} (emitted : Emits globals outer chain frames) :
    frames.IsChain Passes := by
  induction emitted with
  | mixed => exact .singleton _
  | @wrapper outer name parameters locals child head tail free code localDecls childEmitted selected ih =>
    apply ih.cons_cons
    intro binding requested
    have inherited : binding ∈ head.free.map FreeName.source :=
      List.mem_map.mpr ⟨reference binding, requested, rfl⟩
    have inReads := List.mem_append_left [fileSlot child.name] inherited
    exact (selected_member selected binding).trans (and_iff_right inReads)

private theorem local_route {name : String} {outer : List (List String)} {frames : List Frame} {distance : Nat}
    (linked : frames.IsChain (fun child parent => Passes parent child))
    (exclusive : ∀ frame ∈ frames, name ∈ frame.owned → reference (fileSlot name) ∉ frame.free)
    (demand : ∀ head ∈ frames.head?, reference (fileSlot name) ∈ head.free ∨ name ∈ head.owned)
    (nearest : Nearest name (frames.map Frame.owned ++ outer) distance) :
    LocalRoute name outer frames distance := by
  induction frames generalizing distance with
  | nil => exact .outside nearest
  | cons head rest ih =>
    obtain ⟨link, later⟩ := List.isChain_cons.mp linked
    cases nearest with
    | owns here => exact .owns here (exclusive head List.mem_cons_self here)
    | farther absent nearest =>
      have captured := (demand head rfl).resolve_right absent
      apply LocalRoute.forwards absent captured
      refine ih later (fun frame member => exclusive frame (List.mem_cons_of_mem _ member)) ?_ nearest
      intro parent parentHead
      by_cases owns : name ∈ parent.owned
      · exact .inr owns
      · exact .inl ((link parent parentHead (fileSlot name) captured).mpr (.inr owns))

theorem nearest_route {globals : List String} {outer : List (List String)} {chain : Chain}
    {frames : List Frame} {name : String} {distance : Nat}
    (emitted : Emits globals outer chain frames)
    (demand : ∀ leaf ∈ frames.getLast?, reference (fileSlot name) ∈ leaf.free)
    (nearest : Nearest name (frames.reverse.map Frame.owned ++ outer) distance) :
    LocalRoute name outer frames.reverse distance := by
  refine local_route (List.isChain_reverse.mpr (passes_along emitted)) ?_ ?_ nearest
  · intro frame member owner
    exact out_of_owned emitted frame (List.mem_reverse.mp member) name owner
  · intro leaf member
    exact .inl (demand leaf (by simpa using member))

theorem global_route {globals : List String} {outer : List (List String)} {chain : Chain}
    {frames : List Frame} (emitted : Emits globals outer chain frames) (name : String)
    (demand : ∀ leaf ∈ frames.getLast?, reference (globalSlot name) ∈ leaf.free) :
    ∀ frame ∈ frames, reference (globalSlot name) ∈ frame.free := by
  have walk : ∀ frames : List Frame, frames.IsChain (fun child parent => Passes parent child) →
      (∀ leaf ∈ frames.head?, reference (globalSlot name) ∈ leaf.free) →
      ∀ frame ∈ frames, reference (globalSlot name) ∈ frame.free := by
    intro frames linked
    induction frames with
    | nil => intro _ frame member; cases member
    | cons head rest ih =>
      intro demand frame member
      have required := demand head rfl
      rcases List.mem_cons.mp member with rfl | member
      · exact required
      · obtain ⟨link, later⟩ := List.isChain_cons.mp linked
        exact ih later (fun parent h => (link parent h _ required).mpr (.inl rfl)) frame member
  intro frame member
  exact walk frames.reverse (List.isChain_reverse.mpr (passes_along emitted))
    (fun leaf h => demand leaf (by simpa using h)) frame (List.mem_reverse.mpr member)

theorem forwarded_prefix {name : String} {outer : List (List String)} {frames : List Frame} {distance : Nat}
    (route : LocalRoute name outer frames distance) :
    ∀ frame ∈ frames.take distance, reference (fileSlot name) ∈ frame.free ∧ name ∉ frame.owned := by
  induction route with
  | outside => intro frame member; simp at member
  | owns => intro frame member; simp at member
  | forwards absent selected _ ih =>
    intro frame present
    rcases List.mem_cons.mp present with rfl | present
    · exact ⟨selected, absent⟩
    · exact ih frame present

private theorem frame_slots (frame : Frame) :
    frame.declaration.signature.slots ++ frame.declaration.locals = frame.owned.map fileSlot := by
  simp [Frame.declaration, Frame.owned, requiredSignature, Signature.slots, Signature.named, Function.comp_def]

private theorem outside_slots (frame : Frame) (binding : Binding)
    (external : binding.scope = .global ∨ binding.name ∉ frame.owned) :
    binding ∉ frame.declaration.signature.slots ++ frame.declaration.locals := by
  rw [frame_slots]
  intro member
  obtain ⟨name, present, rfl⟩ := List.mem_map.mp member
  exact external.elim (by simp [fileSlot]) (fun absent => absent present)

private theorem receipt_reference {state : State} {entry : FreeName}
    {capture : Silmaril.Languages.Starlark.Lists.Capture} (receipt : ReceivesAddress state entry capture) :
    entry = reference capture.binding := by
  cases receipt <;> rfl

theorem find_receipt {state : State} {free : List FreeName}
    {captures : List Silmaril.Languages.Starlark.Lists.Capture} (installed : Installs state free captures)
    (binding : Binding) (present : reference binding ∈ free) :
    ∃ capture, captures.find? (fun entry => entry.binding == binding) = some capture ∧
      capture.binding = binding ∧ ReceivesAddress state (reference binding) capture := by
  induction installed with
  | nil => cases present
  | @cons entry capture rest later received _ ih =>
    have sameReference := receipt_reference received
    by_cases same : capture.binding = binding
    · refine ⟨capture, by simp [same], same, ?_⟩
      rw [← same, ← sameReference]
      exact received
    · have tail : reference binding ∈ rest :=
        (List.mem_cons.mp present).resolve_left (fun equal =>
          same ((congrArg FreeName.source (equal.trans sameReference)).symm))
      obtain ⟨found, lookup, name, receipt⟩ := ih tail
      exact ⟨found, by simp [same, lookup], name, receipt⟩

private theorem receipt_address {state : State} {binding : Binding}
    {capture : Silmaril.Languages.Starlark.Lists.Capture}
    (receipt : ReceivesAddress state (reference binding) capture) :
    HasAddress state binding capture.address ∧ capture.localCell = (binding.scope == .local) := by
  cases receipt with
  | enclosing slot => exact ⟨.inl slot, rfl⟩
  | forwardedLocal slot => exact ⟨.inr slot, rfl⟩
  | ownedGlobal slot => exact ⟨.inl slot, rfl⟩
  | capturedGlobal slot => exact ⟨.inr slot, rfl⟩

private theorem address_unique {state : State} {binding : Binding} {left right : Address}
    (first : HasAddress state binding left) (second : HasAddress state binding right) : left = right := by
  rcases first with first | first <;> rcases second with second | second <;>
    rw [first] at second <;> cases second <;> rfl

private theorem activate_forwarded (parent : Frame) (owner current : State) (binding : Binding)
    {captures : List Silmaril.Languages.Starlark.Lists.Capture} (installed : Installs owner parent.free captures)
    (arguments : List (Binding × Value)) (present : reference binding ∈ parent.free)
    (external : binding.scope = .global ∨ binding.name ∉ parent.owned) :
    ∃ address, HasAddress owner binding address ∧
      (activate current parent.declaration captures arguments).slots binding =
        some (.captured address (binding.scope == .local)) := by
  obtain ⟨capture, found, name, receipt⟩ := find_receipt installed binding present
  have ⟨address, flag⟩ := receipt_address receipt
  refine ⟨capture.address, address, ?_⟩
  have empty := outside_slots parent binding external
  rw [← name] at found empty
  have same := activate_capture current parent.declaration captures capture arguments found empty
  rw [name, flag] at same
  exact same

private theorem receipt_exists_of_slot {state : State} (binding : Binding) (address : Address)
    (available : HasAddress state binding address) :
    ReceivesAddress state (reference binding) ⟨binding, address, binding.scope == .local⟩ := by
  rcases binding with ⟨scope, name⟩
  cases scope with
  | «local» =>
    rcases available with owned | forwarded
    · exact .enclosing owned
    · exact .forwardedLocal forwarded
  | «global» =>
    rcases available with owned | forwarded
    · exact .ownedGlobal owned
    · exact .capturedGlobal forwarded

theorem installs_of_addresses (state : State) (free : List FreeName)
    (addresses : ∀ entry ∈ free, ∃ binding address, entry = reference binding ∧ HasAddress state binding address) :
    ∃ captures, Installs state free captures := by
  induction free with
  | nil => exact ⟨[], .nil⟩
  | cons entry rest ih =>
    obtain ⟨binding, address, rfl, available⟩ := addresses entry List.mem_cons_self
    obtain ⟨restCaptures, receipts⟩ := ih (fun entry present => addresses entry (List.mem_cons_of_mem _ present))
    exact ⟨_, .cons (receipt_exists_of_slot binding address available) receipts⟩

/-- The new frame contains either a freshly allocated owned slot or an
inherited address for every capture requested by its immediate child. -/
theorem child_installs (parent child : Frame) (owner current : State)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture) (arguments : List (Binding × Value))
    (installed : Installs owner parent.free captures) (connected : Passes parent child)
    (childScoped : child.WellScoped) :
    ∃ received, Installs (activate current parent.declaration captures arguments) child.free received := by
  apply installs_of_addresses
  intro entry present
  obtain ⟨binding, rfl, _⟩ := childScoped entry present
  by_cases external : binding.scope = .global ∨ binding.name ∉ parent.owned
  · have passed := (connected binding present).mpr external
    obtain ⟨address, _, slot⟩ := activate_forwarded parent owner current binding installed arguments passed external
    exact ⟨binding, address, rfl, .inr slot⟩
  · obtain ⟨localSlot, owned⟩ := not_or.mp external
    have declared : binding ∈ parent.declaration.signature.slots ++ parent.declaration.locals := by
      rw [frame_slots]
      refine List.mem_map.mpr ⟨binding.name, Decidable.not_not.mp owned, ?_⟩
      cases binding with
      | mk scope name => cases scope <;> first | rfl | exact (localSlot rfl).elim
    obtain ⟨address, slot⟩ := activate_owned current parent.declaration captures arguments binding declared
    exact ⟨binding, address, rfl, .inl slot⟩

theorem invokes_address {program : Program} {state final : State} {frames : List Frame}
    (invoked : Invokes program state frames final) (binding : Binding) (address : Address)
    (initial : HasAddress state binding address)
    (along : ∀ frame ∈ frames, reference binding ∈ frame.free ∧
      (binding.scope = .global ∨ binding.name ∉ frame.owned)) :
    HasAddress final binding address ∧
      (frames ≠ [] → final.slots binding = some (.captured address (binding.scope == .local))) := by
  induction invoked with
  | nil => exact ⟨initial, by simp⟩
  | @step state created final frame rest id target captures arguments found installed ran cell invoked ih =>
    obtain ⟨requested, outside⟩ := along frame List.mem_cons_self
    obtain ⟨inherited, before, after⟩ := activate_forwarded frame state created binding installed arguments requested outside
    have equal := address_unique before initial
    rw [equal] at after
    obtain ⟨preserved, nonempty⟩ := ih (.inr after) (fun frame member => along frame (List.mem_cons_of_mem _ member))
    refine ⟨preserved, fun _ => ?_⟩
    cases rest with
    | nil => cases invoked; exact after
    | cons => exact nonempty (by simp)

theorem local_address {program : Program} {owner final : State} {frames : List Frame}
    {name : String} {outer : List (List String)} {distance : Nat}
    (route : LocalRoute name outer frames distance)
    (invoked : Invokes program owner (frames.take distance).reverse final) (address : Address)
    (initial : HasAddress owner (fileSlot name) address) :
    HasAddress final (fileSlot name) address ∧
      ((frames.take distance).reverse ≠ [] → final.slots (fileSlot name) = some (.captured address true)) :=
  invokes_address invoked (fileSlot name) address initial fun frame member =>
    let selected := forwarded_prefix route frame (List.mem_reverse.mp member)
    ⟨selected.1, .inr selected.2⟩

theorem global_address {program : Program} {owner final : State} {frames : List Frame}
    {globals : List String} {outer : List (List String)} {chain : Chain}
    (emitted : Emits globals outer chain frames) (name : String)
    (demand : ∀ leaf ∈ frames.getLast?, reference (globalSlot name) ∈ leaf.free)
    (invoked : Invokes program owner frames final) (address : Address)
    (initial : HasAddress owner (globalSlot name) address) :
    HasAddress final (globalSlot name) address ∧
      (frames ≠ [] → final.slots (globalSlot name) = some (.captured address false)) :=
  invokes_address invoked (globalSlot name) address initial fun frame member =>
    ⟨global_route emitted name demand frame member, .inl rfl⟩

theorem invoke_frame (program : Program) (frame : Frame) (id : Nat) (state : State) (target : Binding)
    (address : Address) (before : Option Value) (frozen : Bool)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture) (arguments : List (Binding × Value))
    (found : program[id]? = some frame.declaration) (installed : Installs state frame.free captures)
    (owned : state.slots target = some (.owned address))
    (cell : state.heap[address]? = some ⟨.binding before, frozen⟩) :
    ∃ created, Invokes program state [frame] (activate created frame.declaration captures arguments) := by
  obtain ⟨created, ran, _, stored⟩ := define_installs program frame.declaration id target state state address
    before frozen captures found installed owned cell
  exact ⟨created, .step found installed ran stored (.nil _)⟩

theorem invokes_append {program : Program} {start middle finish : State} {first rest : List Frame}
    (firstRun : Invokes program start first middle) (suffix : Invokes program middle rest finish) :
    Invokes program start (first ++ rest) finish := by
  induction firstRun with
  | nil => exact suffix
  | step found installed ran cell _ ih => exact .step found installed ran cell (ih suffix)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Forwarding
