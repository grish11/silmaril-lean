module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Frame

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

open Assignment (LexicalBlock)
open Functions
open Lists (State Capture Outcome)
open Lists.Iteration (Flow finishState)

/-- The declarative lexical body relation predicts checked compilation. -/
theorem compile_suite {block : LexicalBlock} {source : Suite} {code : Functions.Body} {reads : List Binding}
    (related : Elaborates block source code reads) (program : Program) :
    compileBody ⟨block.context, .local⟩ source.source program = .ok (⟨code, reads⟩, program) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.compile_suite related program

theorem resolves_at {block : LexicalBlock} {source : Lowering.Resolve.SourceExpr}
    {code : Lowering.Expr} {reads : List Binding} (related : Operand block source code reads)
    (initial : List Binding) :
    Lowering.Resolve.resolveExpr block.context source initial = .ok (code, reads.reverse ++ initial) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.resolves_at related initial

theorem evaluates_with (program : Program) (available : List DeclarationId) (calls : Lowering.ClosureRuns available)
    {block : LexicalBlock} {state : State} {source : Lowering.Resolve.SourceExpr}
    {code : Lowering.Expr} {out : Outcome Lists.Value} (ran : Evaluates block state source code out) :
    Lowering.EvaluatesWith program available calls (fun _ => True) state code out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.evaluates_with program available calls ran

theorem operand_total {block : LexicalBlock} {source : Lowering.Resolve.SourceExpr} {code : Lowering.Expr}
    {reads : List Binding} (related : Operand block source code reads) (state : State) :
    ∃ out, Evaluates block state source code out ∧ Keeps state.heap.size state (finishState out) := by
  obtain ⟨out, ran, extendsHeap⟩ :=
    Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.operands_total related state
  exact ⟨out, ran, Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.extends_keeps _ extendsHeap⟩

theorem capture_cells_written (state : State) (target : Binding) (value : Lists.Value) {captures : List Capture}
    (live : CaptureCells state captures) : CaptureCells (state.write target value) captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.capture_cells_written state target value live

/-- Each tracked operand read has a declarative lexical origin. -/
theorem operand_origins {block : LexicalBlock} {source : Lowering.Resolve.SourceExpr}
    {code : Lowering.Expr} {reads : List Binding} (related : Operand block source code reads) :
    ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.operand_origins related

theorem prefix_read_origins {block : LexicalBlock}
    {source : List (String × Lowering.Resolve.SourceExpr)} {code : List (String × Lowering.Expr)}
    {reads : List Binding} (related : ElaboratesPrefix block source code reads) :
    ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.prefix_read_origins related

theorem body_origins {block : LexicalBlock} {source : Suite} {code : Functions.Body} {reads : List Binding}
    (related : Elaborates block source code reads) :
    ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.body_origins related

theorem collects_prefix (source : List (String × Lowering.Resolve.SourceExpr)) {tail : Statement}
    {binders : List String} (collected : Block.BodyBinders tail binders) :
    Block.BodyBinders (prependSource source tail) (source.map Prod.fst ++ binders) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.collects_prefix source collected

theorem collects (body : Suite) : Block.BodyBinders body.source body.binders :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.collects body

theorem prefix_total {block : LexicalBlock} {free : List FreeName} {floor : Nat}
    {source : List (String × Lowering.Resolve.SourceExpr)} {code : List (String × Lowering.Expr)}
    {reads : List Binding} (profile : ElaboratesPrefix block source code reads) (state : State)
    (frame : Frame block free floor state) :
    ∃ out, RunsPrefix block state source code out ∧ Frame block free floor (finishState out) ∧
      Keeps floor state (finishState out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.prefix_total profile state frame

/-- Compile a definition once its recursively compiled body and independent
binder and read order are known. The child table precedes its parent ID. -/
theorem compile_nested_body {globals enclosing : List String} (name : String) (parameters : Parameters)
    {source : Statement} {occurrences locals : List String} (collected : Block.BodyBinders source occurrences)
    (binders : Block.LocalBinders parameters.names occurrences locals)
    (body : ResolvedBody) {free : List FreeName}
    (selected : Selects ⟨parameters.names ++ locals, enclosing, globals⟩ body.reads free)
    (defaults : List PlainPositionalDefault)
    (same : defaults.map (fun item => (item.name, item.source)) = parameters.optional)
    (tracked : ∀ item ∈ defaults, Lowering.Resolve.resolveTracked ⟨enclosing, globals⟩ item.source = .ok (item.value, item.reads))
    (seed middle : Program)
    (compiled : compileBody ⟨(LexicalBlock.mk (parameters.names ++ locals) enclosing globals).context, .local⟩
      source seed = .ok (body, middle)) :
    compileBody ⟨⟨enclosing, globals⟩, .local⟩ (.define name parameters.source source) seed =
      .ok (⟨.define (fileSlot name) middle.size,
          defaults.flatMap PlainPositionalDefault.reads ++ free.map FreeName.source⟩,
        middle.push ⟨parameters.signature (defaults.map PlainPositionalDefault.value), locals.map fileSlot, free, body.code⟩) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.compile_nested_body name parameters
    collected binders body selected defaults same tracked seed middle compiled

/-- The checked child body and resolved defaults fix the emitted declaration. -/
theorem compile_nested {globals enclosing : List String} {definition : Definition}
    (plan : Plan globals definition enclosing) (defaults : List PlainPositionalDefault)
    (same : defaults.map (fun item => (item.name, item.source)) = definition.parameters.optional)
    (tracked : ∀ item ∈ defaults, Lowering.Resolve.resolveTracked ⟨enclosing, globals⟩ item.source =
      .ok (item.value, item.reads))
    (program : Program) :
    compileBody ⟨⟨enclosing, globals⟩, .local⟩
        (.define definition.name definition.parameters.source definition.body.source) program =
      .ok (⟨.define (fileSlot definition.name) program.size,
          defaults.flatMap PlainPositionalDefault.reads ++ plan.free.map FreeName.source⟩,
        program.push (plan.declaration (defaults.map PlainPositionalDefault.value))) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.compile_nested plan defaults same tracked program

/-- An open assignment sequence compiles around an already checked continuation. -/
theorem compile_prefix {block : LexicalBlock} {source : List (String × Lowering.Resolve.SourceExpr)}
    {code : List (String × Lowering.Expr)} {reads : List Binding}
    (related : ElaboratesPrefix block source code reads)
    {tail : Statement} {tailCode : ResolvedBody} {program final : Program}
    (compiled : compileBody ⟨block.context, .local⟩ tail program = .ok (tailCode, final)) :
    compileBody ⟨block.context, .local⟩ (prependSource source tail) program =
      .ok (⟨prependCode code tailCode.code, reads ++ tailCode.reads⟩, final) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.compile_prefix related compiled

/-- The open sequence enters the continuation only on success. Both
semantics retain the reached failure state when an assignment fails. -/
theorem prefix_agrees (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} {state : State} {source : List (String × Lowering.Resolve.SourceExpr)}
    {code : List (String × Lowering.Expr)} {result : Outcome Unit}
    (ran : RunsPrefix block state source code result) (tail : Functions.Body) (out : Outcome Flow)
    (continuation : ∀ middle, result = .ok () middle → denoteBody program available tail middle = out) :
    Exec program available state (prependCode code tail) (result.resume fun _ _ => out) ∧
      denoteBody program available (prependCode code tail) state = (result.resume fun _ _ => out) := by
  have exec := Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.prefix_sound
    program available ran tail out (fun middle reached => (exec_iff_denoteBody _ _ _ _ _).mpr (continuation middle reached))
  exact ⟨exec, (exec_iff_denoteBody _ _ _ _ _).mp exec⟩

/-- The compositional read rule supplies the complete capture selection
after independent collection of the local binders. -/
theorem plan_of_suite (globals : List String) (definition : Definition) (locals : List String)
    {code : Functions.Body} {reads : List Binding}
    (binders : Block.LocalBinders definition.parameters.names definition.body.binders locals)
    (related : Elaborates ⟨definition.parameters.names ++ locals, [], globals⟩ definition.body code reads) :
    Nonempty (Plan globals definition) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.plan_of_suite globals definition locals [] binders related

/-- The same independent selection works in a collected enclosing scope. -/
theorem plan_in_scope (globals : List String) (definition : Definition) (locals enclosing : List String)
    {code : Functions.Body} {reads : List Binding}
    (binders : Block.LocalBinders definition.parameters.names definition.body.binders locals)
    (related : Elaborates ⟨definition.parameters.names ++ locals, enclosing, globals⟩ definition.body code reads) :
    Nonempty (Plan globals definition enclosing) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.plan_of_suite globals definition locals enclosing binders related

theorem signature_slots (parameters : Parameters) (locals : List String) (codes : List Lowering.Expr)
    (length : codes.length = parameters.optional.length) :
    (parameters.signature codes).slots ++ locals.map fileSlot = (parameters.names ++ locals).map fileSlot :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.signature_slots parameters locals codes length

/-- The emitted signature and locals allocate exactly the lexical owned slots. -/
theorem declaration_slots {globals enclosing : List String} {definition : Definition}
    (plan : Plan globals definition enclosing) (codes : List Lowering.Expr)
    (length : codes.length = definition.parameters.optional.length) :
    (plan.declaration codes).signature.slots ++ (plan.declaration codes).locals = plan.block.owned.map fileSlot :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.declaration_slots plan codes length

/-- A scoped activation allocates fresh owned cells and retains the
addresses of selected, live captures. -/
theorem activate_frame (block : LexicalBlock) (declaration : Declaration)
    (slots : declaration.signature.slots ++ declaration.locals = block.owned.map fileSlot)
    (caller : State) (captures : List Capture) (assigned : List (Binding × Lists.Value))
    (selected : ∀ binding, (⟨binding, binding⟩ : FreeName) ∈ declaration.free →
      binding ∉ declaration.signature.slots ++ declaration.locals ∧
      ∃ capture, captures.find? (fun entry => entry.binding == binding) = some capture ∧
        capture.binding = binding ∧ capture.localCell = (binding.scope == .local) ∧
        ∃ value frozen, caller.heap[capture.address]? = some ⟨.binding value, frozen⟩) :
    Frame block declaration.free caller.heap.size (activate caller declaration captures assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.activate_frame
    block declaration slots caller captures assigned selected

/-- Reconstruct the lexical frame from the declaration layout and live
captures at activation. The defining activation can have returned. -/
theorem selected_frame (block : LexicalBlock) (declaration : Declaration)
    (slots : declaration.signature.slots ++ declaration.locals = block.owned.map fileSlot)
    {reads : List Binding} (selected : Selects block reads declaration.free) (caller owner : State)
    (captures : List Capture) (installed : Installs owner declaration.free captures)
    (cells : CaptureCells caller captures) (assigned : List (Binding × Lists.Value)) :
    Frame block declaration.free caller.heap.size (activate caller declaration captures assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.selected_frame block declaration slots
    selected caller owner captures installed cells assigned

theorem frame_preserved {block : LexicalBlock} {free : List FreeName} {floor : Nat} {state next : State}
    (frame : Frame block free floor state) (kept : Keeps state.heap.size state next) :
    Frame block free floor next :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.extend_frame frame
    ⟨kept.1, fun address cell found => kept.2 address cell (Array.getElem?_eq_some_iff.mp found).choose found⟩

theorem written_frame {block : LexicalBlock} {free : List FreeName} {floor : Nat}
    {state : State} {name : String} (member : name ∈ block.owned) (value : Lists.Value)
    (frame : Frame block free floor state) :
    Frame block free floor (state.write (fileSlot name) value) ∧ Keeps floor state (state.write (fileSlot name) value) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.written_frame member value frame

theorem keeps_trans {floor : Nat} {first middle last : State}
    (head : Keeps floor first middle) (tail : Keeps floor middle last) : Keeps floor first last :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.keeps_trans head tail

/-- The return boundary keeps the caller's original slots and cells. -/
theorem returned_keeps (caller : State) (declaration : Declaration) (captures : List Capture)
    (assigned : List (Binding × Lists.Value)) (out : Outcome Flow)
    (kept : Keeps caller.heap.size (activate caller declaration captures assigned)
      (finishState out)) :
    Keeps caller.heap.size caller
      (finishState (Leaf.returnTo caller out)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.returned_keeps
    caller declaration captures assigned out kept

/-- Each reached assignment extends the trace once. A reached error
retains the prior heap and stops the body. The final frame is preserved
and the source outcome agrees exactly with execution and denotation. -/
theorem body_agrees (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} {free : List FreeName} {floor : Nat}
    {source : Suite} {code : Functions.Body} {reads : List Binding}
    (profile : Elaborates block source code reads) (state : State) (frame : Frame block free floor state) :
    ∃ out, Runs block state source code out ∧ Frame block free floor (finishState out) ∧ Keeps floor state (finishState out) ∧
      Exec program available state code out ∧ denoteBody program available code state = out := by
  obtain ⟨out, source, final, kept⟩ :=
    Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.runs_total profile state frame
  have executed := Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.runs_sound program available source
  exact ⟨out, source, final, kept, executed, (exec_iff_denoteBody _ _ _ _ _).mp executed⟩

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
