module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Module

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults

open Functions
open Lists (State Outcome)
open Lists.Iteration (Flow)
open Block (ModuleBinders)

local notation "Value" => Lists.Value

/-- Explicit operands and saved defaults have an independent binding result. -/
theorem binds_total (slots : List (Binding × Option Value)) (values : List Value) :
    ∃ result, Binds slots values result :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.binds_total slots values

/-- The native definition runs the independent default spine and installs
its saved values only on success. The denotation agrees on the full state. -/
theorem definition_sound (program : Program) (available : List DeclarationId) (target : Binding)
    (id : Nat) (parameters : Parameters) (codes : List Lowering.Expr) (declaration : Declaration)
    (found : program[id]? = some declaration)
    (defaults : declaration.signature.defaulted = (parameters.optional.map (fileSlot ∘ Prod.fst)).zip codes)
    (length : codes.length = parameters.optional.length)
    {globals : List String} {state : State} {out : Outcome Flow}
    (source : Defines globals target id declaration.free parameters codes state out) :
    Exec program available state (.define target id) out ∧
      denoteBody program available (.define target id) state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.definition_sound
    program available target id parameters codes declaration found defaults length source

/-- Checked normalized compilation identifies the emitted instruction,
signature and declaration index and supplies the independent default evaluation. -/
theorem checked_definition_site {before after : List Command} {definition : Definition} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ definition.command :: after) globals)
    (checked : resolve (before ++ definition.command :: after) linked = .ok resolved)
    (admitted : Admitted globals definition) (segment : RootCall.Segment globals after) :
    ∃ id codes, resolved.source.commands[before.length]? = some (.exec (.define definition.name id)) ∧
      resolved.program[id]? = some (definition.emitted codes) ∧ codes.length = definition.parameters.optional.length ∧
      ∀ state, ∃ out, Evaluates globals state (definition.parameters.optional.map Prod.snd) codes out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_definition_site
    declared checked admitted segment

/-- Positional preparation respects the active declaration set at a
checked nested call site. -/
theorem checked_prepare_positional {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (available : List DeclarationId)
    (permitted : id ∈ available) (parameters : Parameters)
    (declaration : Declaration) (codes : List Lowering.Expr)
    (found : resolved.program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature codes)
    (codeLength : codes.length = parameters.optional.length)
    (state : State) (address : Nat) (frozen : Bool)
    (captures : List Lists.Capture)
    (defaults actuals : List Value)
    (valueLength : defaults.length = parameters.optional.length)
    (cell : state.heap[address]? = some ⟨.function ⟨id, captures,
      (parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults⟩, frozen⟩)
    {result : Except Lists.Error (List (Binding × Value))}
    (binding : Binds (parameters.slots defaults) actuals result) :
    prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) state =
      match result with
      | .error error => .error error state
      | .ok assigned => .ok (.closure ⟨id, permitted, declaration.body⟩)
        (activate state declaration captures assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_prepare_positional
    checked id available permitted parameters declaration codes found signature codeLength state
    address frozen captures defaults actuals valueLength cell binding

/-- Checked positional preparation applies to any emitted declaration
with this plain signature and its recorded capture vector and defaults. -/
theorem checked_prepare_signature {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (parameters : Parameters)
    (declaration : Declaration) (codes : List Lowering.Expr)
    (found : resolved.program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature codes)
    (codeLength : codes.length = parameters.optional.length)
    (state : State) (address : Nat) (frozen : Bool) (captures : List Lists.Capture)
    (defaults actuals : List Value) (valueLength : defaults.length = parameters.optional.length)
    (cell : state.heap[address]? = some ⟨.function ⟨id, captures,
      (parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults⟩, frozen⟩)
    {result : Except Lists.Error (List (Binding × Value))}
    (binding : Binds (parameters.slots defaults) actuals result) :
    let available := List.range resolved.program.size
    ∃ permitted : id ∈ available,
      prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) state =
        match result with
        | .error error => .error error state
        | .ok assigned => .ok (.closure ⟨id, permitted, declaration.body⟩)
          (activate state declaration captures assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_prepare_signature checked id
    parameters declaration codes found signature codeLength state address frozen captures defaults actuals valueLength cell binding

/-- A later call reads the saved values from the actual function cell.
Preparing the call agrees with the independent positional binder on an
exact activation or an error with its unchanged state. -/
theorem checked_prepare_saved {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (definition : Definition)
    (codes : List Lowering.Expr) (found : resolved.program[id]? = some (definition.emitted codes))
    (codeLength : codes.length = definition.parameters.optional.length)
    (state : State) (address : Nat) (frozen : Bool) (defaults actuals : List Value)
    (valueLength : defaults.length = definition.parameters.optional.length)
    (cell : state.heap[address]? = some ⟨.function ⟨id, [],
      (definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults⟩, frozen⟩)
    {result : Except Lists.Error (List (Binding × Value))}
    (binding : Binds (definition.parameters.slots defaults) actuals result) :
    let available := List.range resolved.program.size
    ∃ permitted : id ∈ available,
      prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) state =
        match result with
        | .error error => .error error state
        | .ok assigned => .ok (.closure ⟨id, permitted, (definition.emitted codes).body⟩)
          (activate state (definition.emitted codes) [] assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_prepare_saved
    checked id definition codes found codeLength state address frozen defaults actuals valueLength cell binding

/-- Successful evaluation determines the new closure cell and every later
positional binding that uses that cell at the same address. -/
theorem checked_installed_defaults {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (definition : Definition)
    (codes : List Lowering.Expr) (found : resolved.program[id]? = some (definition.emitted codes))
    (codeLength : codes.length = definition.parameters.optional.length)
    {globals : List String} {state residual : State}
    {defaults : List Value}
    (evaluated : Evaluates globals state (definition.parameters.optional.map Prod.snd) codes (.ok defaults residual)) :
    let saved := (definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults
    let closure : Lists.Closure := ⟨id, [], saved⟩
    let address := residual.heap.size
    let installed := install (globalSlot definition.name) id [] saved residual
    let available := List.range resolved.program.size
    installed.heap[address]? = some ⟨.function closure, false⟩ ∧
      ∀ (later : State) (frozen : Bool)
        (actuals : List Value),
        later.heap[address]? = some ⟨.function closure, frozen⟩ →
        ∃ result, Binds (definition.parameters.slots defaults) actuals result ∧
          ∃ permitted : id ∈ available,
            prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) later =
              match result with
              | .error error => .error error later
              | .ok assigned => .ok (.closure ⟨id, permitted, (definition.emitted codes).body⟩)
                (activate later (definition.emitted codes) [] assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_installed_defaults
    checked id definition codes found codeLength evaluated

/-- The bounded source module derives its reached trace and exact
publication or residual state from checked intake. -/
theorem checked_module {before after : List Command} {definition : Definition}
    (profile : ModuleProfile before after definition) {linked : Program} {resolved : ResolvedModule}
    (checked : resolve (before ++ definition.command :: after) linked = .ok resolved)
    (host : Catalog) (caller : State) :
    let commands := before ++ definition.command :: after
    let globals := names commands
    ∃ out published,
      Wrapper.ReachedPrefix (Defaults.Step resolved globals) 0 (enter resolved.source caller) commands out ∧
      Leaf.Finishes globals caller out published ∧
      Initializes commands host caller linked (.ok published) ∧ runModule commands host caller linked = .ok published :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_module profile checked host caller

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
