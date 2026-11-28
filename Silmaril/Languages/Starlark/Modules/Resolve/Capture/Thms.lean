module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Block.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture

open Assignment
open Block
open Functions (FreeName Declaration Program captureName define activate restoreCaller)
open Functions.Lowering.Resolve (resolveTracked)
open Functions.Comprehensions (assignPatternCode directStages)
open Lists (Address State)

theorem selects_exists (block : LexicalBlock) {body : Statement} {reads : List Binding}
    (resolved : BodyReads block body reads) : ∃ free, Selects block reads free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.selects_exists block resolved

theorem selects_of_origins (block : LexicalBlock) {reads : List Binding}
    (known : ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin) : ∃ free, Selects block reads free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.selects_of_origins block known

theorem installs_lookup (state : State) {free : List FreeName} {captures : List Lists.Capture}
    (related : Installs state free captures) : free.mapM (captureName state) = .ok captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.capture_addresses state related

/-- Equal slot maps preserve all owned and forwarded capture addresses. -/
theorem installs_in_same_slots {active final : State} {free : List FreeName} {captures : List Lists.Capture}
    (slots : final.slots = active.slots) (installed : Installs active free captures) : Installs final free captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.installs_in_same_slots slots installed

theorem captureNames_eq {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selected : Selects block reads free) : captureNames block.owned reads = free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.capture_names selected

/-- A read is selected exactly when it is a global or outside the local block. -/
theorem selected_member {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selected : Selects block reads free) (binding : Binding) :
    (⟨binding, binding⟩ : FreeName) ∈ free ↔
      binding ∈ reads ∧ (binding.scope = .global ∨ binding.name ∉ block.owned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.selected_member selected binding

/-- An ordered capture keeps the original lexical binding at each end. -/
theorem selected_origin {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selected : Selects block reads free) (entry : FreeName) (present : entry ∈ free) :
    ∃ binding, entry = ⟨binding, binding⟩ ∧
      (ReadOrigin block binding .enclosing ∨ ReadOrigin block binding .module) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.selected_origin selected entry present

theorem required_parameter_binders (parameters : List String) :
    ParameterBinders (.required parameters) parameters :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.required_binders parameters

/-- Independently selected captures are outside the owned frame. -/
theorem selected_outside_owned {block : LexicalBlock} {reads : List Binding} {free : List FreeName}
    (selected : Selects block reads free) (entry : FreeName) (member : entry ∈ free)
    (name : String) (owned : name ∈ block.owned) : entry.target ≠ fileSlot name :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.selected_outside_owned selected entry member name owned

/-- In a load-free module the immediate parent's local names are precisely
its own parameters and local declarations. -/
theorem parent_layout (commands : List Command) (globals : List String)
    (declared : ModuleBinders commands globals) (signature : SourceSignature) (body : Statement)
    (parameters occurrences locals : List String) (parameterDecls : ParameterBinders signature parameters)
    (bodyDecls : BodyBinders body occurrences) (localDecls : LocalBinders parameters occurrences locals) :
    collectFunctionLayout (moduleBlock commands).reads signature body =
      .ok ⟨locals, ⟨⟨parameters ++ locals, globals⟩, .local⟩⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.parent_layout commands globals declared signature body
    parameters occurrences locals parameterDecls bodyDecls localDecls

/-- The emitted declaration for a nested mixed assignment and return
contains exactly the independently selected references. Its parent context
can be supplied by the load-free module layout theorem. -/
theorem mixed_definition (parent : BlockContext) (name : String) (parameters locals : List String)
    (body : MixedBody) (localDecls : LocalBinders parameters [body.destination] locals)
    (targetProfile : TargetInProfile .local body.target) (rhsProfile : RhsInProfile body.rhs)
    (returnProfile : OperandInProfile body.returned) (program next : Program)
    (assignment : ResolvedPatternAssignment) (returned : Functions.Lowering.Expr) (returnReads : List Binding)
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
            .seq (assignPatternCode assignment.pattern assignment.rhs directStages) (.returnExpr returned)⟩) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.mixed_definition parent name parameters locals body localDecls
    targetProfile rhsProfile returnProfile program next assignment returned returnReads assigned resolvedReturn

/-- Carry the source assignment and return evidence on the exact emitted body. -/
theorem mixed_definition_linked (parent : BlockContext) (name : String) (parameters locals : List String)
    (body : MixedBody) (localDecls : LocalBinders parameters [body.destination] locals)
    (targetProfile : TargetInProfile .local body.target) (rhsProfile : RhsInProfile body.rhs)
    (returnProfile : OperandInProfile body.returned) (program next : Program)
    (assignment : ResolvedPatternAssignment) (returned : Functions.Lowering.Expr) (returnReads : List Binding)
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
            .seq (assignPatternCode assignment.pattern assignment.rhs directStages) (.returnExpr returned)⟩) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.mixed_definition_linked parent name parameters locals body localDecls
    targetProfile rhsProfile returnProfile program next assignment returned returnReads assigned resolvedReturn

/-- Definition copies slot addresses into the function object. The selected
slots need only exist at creation. Restoring the caller leaves the new cell
in the heap, so a returned reference can use the same environment. -/
theorem define_installs (program : Program) (declaration : Declaration) (id : Nat)
    (target : Binding) (state caller : State) (targetAddress : Address)
    (before : Option Lists.Value) (frozen : Bool) (captures : List Lists.Capture)
    (found : program[id]? = some declaration) (related : Installs state declaration.free captures)
    (owned : state.slots target = some (.owned targetAddress))
    (cell : state.heap[targetAddress]? = some ⟨.binding before, frozen⟩) :
    ∃ next, define program target id [] state = .ok .next next ∧
      next.bindingValue target = .ok (.function state.heap.size) ∧
      (restoreCaller caller next).heap[state.heap.size]? = some ⟨.function ⟨id, captures, []⟩, false⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.define_installs program declaration id target state caller
    targetAddress before frozen captures found related owned cell

/-- Allocating the callee's parameters and locals supplies owned slots. -/
theorem activate_owned (state : State) (declaration : Declaration) (captures : List Lists.Capture)
    (arguments : List (Binding × Lists.Value)) (binding : Binding)
    (declared : binding ∈ declaration.signature.slots ++ declaration.locals) :
    ∃ address, (activate state declaration captures arguments).slots binding = some (.owned address) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.activate_owned state declaration captures arguments binding declared

/-- Activation installs the saved address when the binding is outside the
callee's owned slots. Allocating parameters and locals preserves it. -/
theorem activate_capture (state : State) (declaration : Declaration)
    (captures : List Lists.Capture) (capture : Lists.Capture) (arguments : List (Binding × Lists.Value))
    (found : captures.find? (fun entry => entry.binding == capture.binding) = some capture)
    (disjoint : capture.binding ∉ declaration.signature.slots ++ declaration.locals) :
    (activate state declaration captures arguments).slots capture.binding =
      some (.captured capture.address capture.localCell) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.activate_capture state declaration captures capture
    arguments found disjoint

/-- For a declaration with independently selected captures, its owned
parameters and locals cannot replace an installed capture. -/
theorem activate_selected (parent : BlockContext) (parameters locals : List String)
    {reads : List Binding} {free : List FreeName} (selected : Selects (childBlock parent parameters locals) reads free)
    (owner current : State) (code : Functions.Body)
    (captures : List Lists.Capture) (capture : Lists.Capture)
    (installed : Installs owner free captures) (arguments : List (Binding × Lists.Value))
    (found : captures.find? (fun entry => entry.binding == capture.binding) = some capture) :
    (activate current ⟨requiredSignature parameters, locals.map fileSlot, free, code⟩ captures arguments).slots
      capture.binding = some (.captured capture.address capture.localCell) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.activate_selected parent parameters locals selected
    owner current code captures capture installed arguments found

/-- Reading an installed capture consults the current binding cell and
fails if its owner has yet to initialize it. -/
theorem read_uninitialized_capture (state : State) (binding : Binding) (address : Address)
    (localCell frozen : Bool) (slot : state.slots binding = some (.captured address localCell))
    (cell : state.heap[address]? = some ⟨.binding none, frozen⟩) :
    state.bindingValue binding = .error (.uninitialized binding) := by
  simp only [State.bindingValue, slot, Lists.Slot.address, cell]

/-- An assignment through the defining frame's owned slot is visible
through the same address in the callee. This updates the binding cell. -/
theorem read_after_rebind (owner callee : State) (binding captured : Binding) (address : Address)
    (localCell frozen : Bool) (before : Option Lists.Value) (value : Lists.Value)
    (owned : owner.slots binding = some (.owned address))
    (cell : owner.heap[address]? = some ⟨.binding before, frozen⟩)
    (installed : callee.slots captured = some (.captured address localCell)) :
    (restoreCaller callee (owner.write binding value)).bindingValue captured = .ok value :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.read_after_rebind owner callee binding captured address
    localCell frozen before value owned cell installed

end Silmaril.Languages.Starlark.Modules.Resolve.Capture
