module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Block.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment
open Silmaril.Languages.Starlark.Modules.Resolve.Block
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Functions (FreeName Declaration Program Signature captureName define activate capturedSlots
  restoreCaller)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (resolveTracked)
open Silmaril.Languages.Starlark.Functions.Lowering (Expr)
open Silmaril.Languages.Starlark.Functions.Comprehensions (AssignmentPattern assignPatternCode directStages)
open Silmaril.Languages.Starlark.Lists (State Slot Address)

local notation "Operand" => Silmaril.Languages.Starlark.Functions.Lowering.Resolve.SourceExpr

private abbrev Known (block : LexicalBlock) (reads : List Binding) :=
  ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin

private theorem read_origin {block : LexicalBlock} {name : String}
    {value : Silmaril.Languages.Starlark.Functions.Lowering.Expr} {reads : List Binding}
    (resolved : ReadResolves block name value reads) : Known block reads := by
  intro binding member
  cases resolved with
  | owned owned =>
    cases List.mem_singleton.mp member
    exact ⟨_, .owned owned⟩
  | enclosing hidden enclosing =>
    cases List.mem_singleton.mp member
    exact ⟨_, .enclosing hidden enclosing⟩
  | global hidden outer global =>
    cases List.mem_singleton.mp member
    exact ⟨_, .module hidden outer global⟩
  | constant | builtin => simp at member

private theorem known_append {block : LexicalBlock} {first rest : List Binding}
    (left : Known block first) (right : Known block rest) : Known block (first ++ rest) :=
  fun binding member => (List.mem_append.mp member).elim (left binding) (right binding)

private theorem operand_reads {block : LexicalBlock} {source : Operand}
    {value : Silmaril.Languages.Starlark.Functions.Lowering.Expr} {reads : List Binding}
    (resolved : OperandResolves block source value reads) : Known block reads := by
  induction resolved with
  | read _ resolution => exact read_origin resolution
  | int | string => intro binding member; cases member
  | index _ _ left right => exact known_append left right
  | call _ related => exact related

private theorem inOrder_preimage {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (ordered : InOrder relation inputs outputs) {out : β} (member : out ∈ outputs) :
    ∃ source ∈ inputs, relation source out := by
  induction ordered with
  | nil => simp at member
  | @cons first image rest images head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨first, List.mem_cons_self, head⟩
    · obtain ⟨source, present, related⟩ := ih member
      exact ⟨source, List.mem_cons_of_mem _ present, related⟩

private theorem pattern_reads {block : LexicalBlock} {source : AssignmentPattern Operand}
    {output : AssignmentPattern × List Binding} (resolved : PatternResolves block source output) :
    Known block output.2 := by
  induction source using (measure (sizeOf : AssignmentPattern Operand → Nat)).wf.induction
      generalizing output with
  | h source ih =>
    cases resolved with
    | name => intro binding member; cases member
    | subscript receiver index => exact known_append (operand_reads receiver) (operand_reads index)
    | @sequence children outputs ordered =>
      intro binding member
      obtain ⟨out, present, read⟩ := List.mem_flatMap.mp member
      obtain ⟨child, belongs, related⟩ := inOrder_preimage ordered present
      exact ih child (by simp_wf; have := List.sizeOf_lt_of_mem belongs; omega) related binding read

private theorem outside_generator (block : LexicalBlock) (generator : String) (binding : Binding)
    {origin : Origin} (related : ReadOrigin { block with owned := generator :: block.owned } binding origin)
    (different : binding ≠ fileSlot generator) : ReadOrigin block binding origin := by
  cases related with
  | owned member =>
    rcases List.mem_cons.mp member with rfl | member
    · exact (different rfl).elim
    · exact .owned member
  | enclosing hidden outer =>
    exact .enclosing (fun member => hidden (List.mem_cons_of_mem _ member)) outer
  | module hidden outer global =>
    exact .module (fun member => hidden (List.mem_cons_of_mem _ member)) outer global

private theorem rhs_reads {block : LexicalBlock} {rhs : CompExpr}
    {value : Silmaril.Languages.Starlark.Functions.Comprehensions.Expression} {reads : List Binding}
    (resolved : RhsResolves block rhs value reads) : Known block reads := by
  cases resolved with
  | plain operand => exact operand_reads operand
  | @list generator iterable element iterated emitted outer inner outerRelated innerRelated =>
    refine known_append (operand_reads outerRelated) ?_
    intro binding member
    obtain ⟨read, kept⟩ := List.mem_filter.mp member
    obtain ⟨origin, related⟩ := operand_reads innerRelated binding read
    exact ⟨origin, outside_generator block generator binding related (by
      intro same
      simp [same] at kept)⟩

private theorem body_reads {block : LexicalBlock} {body : Statement} {reads : List Binding}
    (resolved : BodyReads block body reads) : Known block reads := by
  cases resolved with
  | mixedReturn right left tail =>
    obtain ⟨_, _, target⟩ := left
    exact known_append (known_append (rhs_reads right) (pattern_reads target)) (operand_reads tail)

theorem selects_of_origins (block : LexicalBlock) {reads : List Binding}
    (known : ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin) : ∃ free, Selects block reads free := by
  induction reads using (measure (List.length : List Binding → Nat)).wf.induction with
  | h reads ih =>
    cases reads with
    | nil => exact ⟨[], .nil⟩
    | cons first rest =>
      obtain ⟨origin, related⟩ := known first List.mem_cons_self
      obtain ⟨_, remaining⟩ := ih (rest.filter fun later => !(later == first))
        (Nat.lt_succ_of_le (List.length_filter_le _ _))
        (fun binding member => known binding (List.mem_cons_of_mem _ (List.mem_filter.mp member).1))
      cases origin with
      | owned => exact ⟨_, .owned related remaining⟩
      | enclosing => exact ⟨_, .enclosing related remaining⟩
      | module => exact ⟨_, .module related remaining⟩

theorem selects_exists (block : LexicalBlock) {body : Statement} {reads : List Binding}
    (resolved : BodyReads block body reads) : ∃ free, Selects block reads free :=
  selects_of_origins block (body_reads resolved)

theorem capture_names {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selection : Selects block reads free) : captureNames block.owned reads = free := by
  induction selection with
  | nil => rfl
  | owned related _ ih =>
    cases related with
    | owned member =>
      simpa [captureNames, List.eraseDups_cons, fileSlot, member] using ih
  | enclosing related _ ih =>
    cases related with
    | enclosing missing _ =>
      simp [captureNames, List.eraseDups_cons, fileSlot, missing]
      simpa [captureNames, fileSlot] using ih
  | module related _ ih =>
    cases related with
    | module =>
      simp [captureNames, List.eraseDups_cons, globalSlot]
      simpa [captureNames, globalSlot] using ih

theorem capture_addresses (state : State) {free : List FreeName} {captures : List Silmaril.Languages.Starlark.Lists.Capture}
    (related : Installs state free captures) : free.mapM (captureName state) = .ok captures := by
  induction related with
  | nil => rfl
  | @cons first capture rest captures head _ ih =>
    have one : captureName state first = .ok capture := by
      cases head <;> simp_all [captureName, fileSlot, globalSlot]
    rw [List.mapM_cons, one, ih]
    rfl

private theorem required_order (parameters : List String) :
    InOrder (fun parameter name => parameter.name = name)
      (SourceSignature.required parameters).positional parameters := by
  induction parameters with
  | nil => exact .nil
  | cons first rest ih => exact .cons rfl ih

theorem required_binders (parameters : List String) :
    ParameterBinders (.required parameters) parameters := by
  simpa [SourceSignature.required] using (ParameterBinders.signature none none (required_order parameters) .nil)

private theorem mixed_binders (body : MixedBody) : BodyBinders body.statement [body.destination] :=
  .seq (.pattern ⟨_, .tuple (.cons (.name body.destination)
    (.cons (.subscript body.receiver body.index) .nil))⟩) (.ret _)

theorem parent_layout (commands : List Command) (globals : List String)
    (declared : ModuleBinders commands globals) (signature : SourceSignature) (body : Statement)
    (parameters occurrences locals : List String) (parameterDecls : ParameterBinders signature parameters)
    (bodyDecls : BodyBinders body occurrences) (localDecls : LocalBinders parameters occurrences locals) :
    collectFunctionLayout (moduleBlock commands).reads signature body =
      .ok ⟨locals, ⟨⟨parameters ++ locals, globals⟩, .local⟩⟩ := by
  rw [moduleBlock_eq declared, collectFunctionLayout_eq _ parameterDecls bodyDecls localDecls]
  simp [LexicalBlock.context]

theorem mixed_definition_linked (parent : BlockContext) (name : String) (parameters locals : List String)
    (body : MixedBody) (localDecls : LocalBinders parameters [body.destination] locals)
    (targetProfile : TargetInProfile .local body.target) (rhsProfile : RhsInProfile body.rhs)
    (returnProfile : OperandInProfile body.returned) (program next : Program)
    (assignment : ResolvedPatternAssignment) (returned : Expr) (returnReads : List Binding)
    (assigned : (do
      let layout ← collectFunctionLayout parent.reads (.required parameters) body.statement
      elaboratePatternAssignment layout.block.reads layout.block.writes body.target body.rhs program) =
      .ok (assignment, next))
    (resolvedReturn : resolveTracked (childBlock parent parameters locals).context body.returned =
      .ok (returned, returnReads)) :
    ∃ free,
      LeafCode (childBlock parent parameters locals) body
        (.seq (assignPatternCode assignment.pattern assignment.rhs directStages) (.returnExpr returned)) ∧
      BodyReads (childBlock parent parameters locals) body.statement
          ((assignment.rhsReads ++ assignment.targetReads) ++ returnReads) ∧
      Selects (childBlock parent parameters locals) ((assignment.rhsReads ++ assignment.targetReads) ++ returnReads)
        free ∧
      compileBody parent (.define name (.required parameters) body.statement) program =
        .ok (⟨.define (fileSlot name) program.size, free.map FreeName.source⟩,
          program.push ⟨requiredSignature parameters, locals.map fileSlot, free,
            .seq (assignPatternCode assignment.pattern assignment.rhs directStages) (.returnExpr returned)⟩) := by
  have parameterDecls := required_binders parameters
  have bodyDecls := mixed_binders body
  obtain ⟨related, _, table⟩ := function_assignment_sound parent.reads (.required parameters) body.statement
    parameters [body.destination] locals parameterDecls bodyDecls localDecls body.target body.rhs
    (.first .here) targetProfile rhsProfile program next assignment assigned
  subst next
  have returnedRelated := resolveOperand_sound _ returnProfile resolvedReturn
  have bodyRelated : BodyReads (childBlock parent parameters locals) body.statement
      ((assignment.rhsReads ++ assignment.targetReads) ++ returnReads) :=
    .mixedReturn related.rhsResolves related.targetResolves returnedRelated
  obtain ⟨free, selected⟩ := selects_exists _ bodyRelated
  let block : BlockContext := ⟨(childBlock parent parameters locals).context, .local⟩
  have collected : collectFunctionLayout parent.reads (.required parameters) body.statement = .ok ⟨locals, block⟩ :=
    collectFunctionLayout_eq _ parameterDecls bodyDecls localDecls
  rw [collected] at assigned
  have compiled := compileBody_mixedReturn block body.destination body.receiver body.index body.returned body.rhs
    program program assignment returned returnReads assigned resolvedReturn
  have exactDefinition := compileBody_requiredDefinition parent name parameters body.statement program program
    ⟨locals, block⟩ _ collected compiled
  have exactCaptures := capture_names selected
  change captureNames (parameters ++ locals) _ = free at exactCaptures
  exact ⟨free, .linked assignment returned returnReads related returnedRelated, bodyRelated, selected, by simpa only [exactCaptures] using exactDefinition⟩

theorem mixed_definition (parent : BlockContext) (name : String) (parameters locals : List String)
    (body : MixedBody) (localDecls : LocalBinders parameters [body.destination] locals)
    (targetProfile : TargetInProfile .local body.target) (rhsProfile : RhsInProfile body.rhs)
    (returnProfile : OperandInProfile body.returned) (program next : Program)
    (assignment : ResolvedPatternAssignment) (returned : Expr) (returnReads : List Binding)
    (assigned : (do
      let layout ← collectFunctionLayout parent.reads (.required parameters) body.statement
      elaboratePatternAssignment layout.block.reads layout.block.writes body.target body.rhs program) =
      .ok (assignment, next))
    (resolvedReturn : resolveTracked (childBlock parent parameters locals).context body.returned =
      .ok (returned, returnReads)) :
    ∃ free,
      BodyReads (childBlock parent parameters locals) body.statement
          ((assignment.rhsReads ++ assignment.targetReads) ++ returnReads) ∧
      Selects (childBlock parent parameters locals) ((assignment.rhsReads ++ assignment.targetReads) ++ returnReads)
        free ∧
      compileBody parent (.define name (.required parameters) body.statement) program =
        .ok (⟨.define (fileSlot name) program.size, free.map FreeName.source⟩,
          program.push ⟨requiredSignature parameters, locals.map fileSlot, free,
            .seq (assignPatternCode assignment.pattern assignment.rhs directStages) (.returnExpr returned)⟩) := by
  obtain ⟨free, _, related, selected, compiled⟩ := mixed_definition_linked parent name parameters locals body localDecls
    targetProfile rhsProfile returnProfile program next assignment returned returnReads assigned resolvedReturn
  exact ⟨free, related, selected, compiled⟩

private theorem write_keeps_slots (state : State) (binding : Binding)
    (value : Silmaril.Languages.Starlark.Lists.Value) : (state.write binding value).slots = state.slots := by
  unfold State.write
  split
  · rfl
  · rfl
  · split <;> rfl

theorem define_installs (program : Program) (declaration : Declaration) (id : Nat)
    (target : Binding) (state caller : State) (targetAddress : Address)
    (before : Option Silmaril.Languages.Starlark.Lists.Value) (frozen : Bool)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (found : program[id]? = some declaration) (related : Installs state declaration.free captures)
    (owned : state.slots target = some (.owned targetAddress))
    (cell : state.heap[targetAddress]? = some ⟨.binding before, frozen⟩) :
    ∃ next, define program target id [] state = .ok .next next ∧
      next.bindingValue target = .ok (.function state.heap.size) ∧
      (restoreCaller caller next).heap[state.heap.size]? = some ⟨.function ⟨id, captures, []⟩, false⟩ := by
  have fits := (Array.getElem?_eq_some_iff.mp cell).choose
  have different : targetAddress ≠ state.heap.size := Nat.ne_of_lt fits
  let newCell : Silmaril.Languages.Starlark.Lists.Cell := ⟨.function ⟨id, captures, []⟩, false⟩
  let added := { state with heap := state.heap.push newCell }
  let value := Silmaril.Languages.Starlark.Lists.Value.function state.heap.size
  let next := added.write target value
  have updated : next.heap = added.heap.setIfInBounds targetAddress ⟨.binding (some value), frozen⟩ := by
    simp [next, added, State.write, owned, Array.getElem?_push, different, cell]
  have bounded : targetAddress < added.heap.size := by
    simpa only [added, Array.size_push] using (Nat.lt_succ_of_le (Nat.le_of_lt fits))
  have slot : next.slots target = some (.owned targetAddress) :=
    (congrFun (write_keeps_slots added target value) target).trans owned
  refine ⟨next, by simp [define, found, capture_addresses state related, next, added, newCell, value], ?_, ?_⟩
  · simp [State.bindingValue, slot, Slot.address, updated, bounded, value]
  · simp [restoreCaller, updated, added, different, newCell]

private theorem write_arguments_keep_slots (arguments : List (Binding × Silmaril.Languages.Starlark.Lists.Value))
    (state : State) : (arguments.foldl (fun next (binding, value) => next.write binding value) state).slots =
      state.slots := by
  induction arguments generalizing state with
  | nil => rfl
  | cons arg rest ih => exact (ih _).trans (write_keeps_slots _ _ _)

theorem activate_owned (state : State) (declaration : Declaration)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (arguments : List (Binding × Silmaril.Languages.Starlark.Lists.Value)) (binding : Binding)
    (declared : binding ∈ declaration.signature.slots ++ declaration.locals) :
    ∃ address, (activate state declaration captures arguments).slots binding = some (.owned address) := by
  have allocated (bindings : List Binding) (initial : State)
      (present : binding ∈ bindings ∨ ∃ address, initial.slots binding = some (.owned address)) :
      ∃ address, (bindings.foldl State.allocateSlot initial).slots binding = some (.owned address) := by
    induction bindings generalizing initial with
    | nil => exact present.resolve_left (by simp)
    | cons first rest ih =>
      rw [List.foldl_cons]
      by_cases same : binding = first
      · exact ih _ (.inr ⟨initial.heap.size, by simp [State.allocateSlot, same]⟩)
      · apply ih _
        rcases present with member | ⟨address, slot⟩
        · exact .inl ((List.mem_cons.mp member).resolve_left same)
        · exact .inr ⟨address, by simp [State.allocateSlot, same, slot]⟩
  unfold activate
  rw [write_arguments_keep_slots]
  exact allocated _ _ (.inl declared)

theorem activate_capture (state : State) (declaration : Declaration)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture) (capture : Silmaril.Languages.Starlark.Lists.Capture)
    (arguments : List (Binding × Silmaril.Languages.Starlark.Lists.Value))
    (found : captures.find? (fun entry => entry.binding == capture.binding) = some capture)
    (disjoint : capture.binding ∉ declaration.signature.slots ++ declaration.locals) :
    (activate state declaration captures arguments).slots capture.binding =
      some (.captured capture.address capture.localCell) := by
  have allocateSlots (bindings : List Binding) (initial : State) (outside : capture.binding ∉ bindings) :
      (bindings.foldl State.allocateSlot initial).slots capture.binding = initial.slots capture.binding := by
    induction bindings generalizing initial with
    | nil => rfl
    | cons binding rest ih =>
      have different : capture.binding ≠ binding := fun eq => outside (List.mem_cons.mpr (.inl eq))
      rw [List.foldl_cons, ih _ (fun mem => outside (List.mem_cons_of_mem _ mem))]
      simp [State.allocateSlot, different]
  unfold activate
  rw [write_arguments_keep_slots, allocateSlots _ _ disjoint]
  simp [capturedSlots, found]

theorem selected_outside_owned {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selected : Selects block reads free) (entry : FreeName) (present : entry ∈ free)
    (name : String) (owned : name ∈ block.owned) : entry.target ≠ fileSlot name := by
  induction selected with
  | nil => cases present
  | owned _ _ ih => exact ih present
  | enclosing origin _ ih =>
    rcases List.mem_cons.mp present with rfl | member
    · cases origin with
      | @enclosing enclosingName missing _ =>
        intro equal
        have same : enclosingName = name := congrArg Binding.name equal
        exact missing (same.symm ▸ owned)
    · exact ih member
  | module origin _ ih =>
    rcases List.mem_cons.mp present with rfl | member
    · cases origin
      intro equal
      cases congrArg Binding.scope equal
    · exact ih member

theorem activate_selected (parent : BlockContext) (parameters locals : List String)
    {reads : List Binding} {free : List FreeName} (selected : Selects (childBlock parent parameters locals) reads free)
    (owner current : State) (code : Silmaril.Languages.Starlark.Functions.Body)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture) (capture : Silmaril.Languages.Starlark.Lists.Capture)
    (installed : Installs owner free captures) (arguments : List (Binding × Silmaril.Languages.Starlark.Lists.Value))
    (found : captures.find? (fun entry => entry.binding == capture.binding) = some capture) :
    (activate current ⟨requiredSignature parameters, locals.map fileSlot, free, code⟩ captures arguments).slots
      capture.binding = some (.captured capture.address capture.localCell) := by
  obtain ⟨source, member, address⟩ := inOrder_preimage installed (List.mem_of_find?_eq_some found)
  have same : source.target = capture.binding := by cases address <;> rfl
  refine activate_capture _ _ _ _ _ found ?_
  intro overlaps
  have parameterSlots : (requiredSignature parameters).slots = parameters.map fileSlot := by
    simp [requiredSignature, Signature.slots, Signature.named, Function.comp_def]
  change capture.binding ∈ (requiredSignature parameters).slots ++ locals.map fileSlot at overlaps
  rw [parameterSlots, ← List.map_append] at overlaps
  obtain ⟨name, owned, equal⟩ := List.mem_map.mp overlaps
  exact selected_outside_owned selected source member name owned (same.trans equal.symm)

theorem read_after_rebind (owner callee : State) (binding captured : Binding) (address : Address)
    (localCell frozen : Bool) (before : Option Silmaril.Languages.Starlark.Lists.Value)
    (value : Silmaril.Languages.Starlark.Lists.Value)
    (owned : owner.slots binding = some (.owned address))
    (cell : owner.heap[address]? = some ⟨.binding before, frozen⟩)
    (installed : callee.slots captured = some (.captured address localCell)) :
    (restoreCaller callee (owner.write binding value)).bindingValue captured = .ok value := by
  have fits := (Array.getElem?_eq_some_iff.mp cell).choose
  have changed : (owner.write binding value).heap[address]? = some ⟨.binding (some value), frozen⟩ := by
    simp only [State.write, owned, cell]
    simp [fits]
  simp [State.bindingValue, restoreCaller, installed, Slot.address, changed]

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture
