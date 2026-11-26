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
