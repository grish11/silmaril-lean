module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Run

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence

open Assignment (LexicalBlock)
open Functions
open Lists (State Outcome)
open Lists.Iteration (Flow finishState)

/-- The declarative sequence agrees with the existing normalized compiler. -/
theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.compiles profile

theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    ∃ occurrences, Block.BodyBinders source occurrences :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.collects profile

theorem preserves_declarations {block : LexicalBlock} {source : Statement}
    {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    PreservesDeclarations seed final :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.preserves_declarations profile

theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) :
    ∃ free, Selects block resolved.reads free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.selects profile

/-- Shared execution rule for a prefix, a reached definition, and its tail. -/
theorem runs_definition (program : Program) (available : List DeclarationId) {block : LexicalBlock}
    {source : List (String × Lowering.Resolve.SourceExpr)} {leading : List (String × Lowering.Expr)}
    {reads : List Binding} (leadingProfile : Body.ElaboratesPrefix block source leading reads)
    {name : String} {parameters : Parameters} {items : List PlainPositionalDefault}
    (target : name ∈ block.owned) (lexical : Lexical.Elaborates block parameters.optional items)
    {id : DeclarationId} {child rest : Statement} {tail : Body} {childFree free : List FreeName}
    {state : State} {floor : Nat} (frame : Body.Frame block free floor state)
    (definition : ∀ active, Body.Frame block free floor active →
      ∃ captures out, Installs active childFree captures ∧
        Nested.SiteResult block name parameters items id captures active out ∧
        Exec program available active (.define (fileSlot name) id) out)
    (remaining : ∀ active, Body.Frame block free floor active →
      ∃ out, Runs block active rest tail out ∧ Body.Frame block free floor (finishState out) ∧
        Body.Keeps floor active (finishState out) ∧ Exec program available active tail out) :
    let code := Body.prependCode leading (.seq (.define (fileSlot name) id) tail)
    ∃ out, Runs block state (Body.prependSource source (.seq (.define name parameters.source child) rest)) code out ∧
      Body.Frame block free floor (finishState out) ∧ Body.Keeps floor state (finishState out) ∧
      Exec program available state code out ∧ denoteBody program available code state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.runs_definition
    program available leadingProfile target lexical frame definition remaining

/-- Execute a checked suite from its active frame. A reached definition
derives its declaration lookup and ordered captures, then hands its
installed state to the remaining source. Each error stops immediately. -/
theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    (profile : Elaborates block source seed resolved final) (program : Program)
    (linked : PreservesDeclarations final program) (available : List DeclarationId)
    {before after : List Binding} {free : List FreeName}
    (selection : Selects block (before ++ resolved.reads ++ after) free) (state : State) {floor : Nat}
    (frame : Body.Frame block free floor state) :
    ∃ out, Runs block state source resolved.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec program available state resolved.code out ∧
      denoteBody program available resolved.code state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.runs profile
    program linked available selection state frame

/-- In the supported copy assignment, reading the alias as a later
callee operand yields the very closure installed by the definition. -/
theorem reads_installed_alias_defaults {block : LexicalBlock} {name aliasName : String} {parameters : Parameters}
    {items : List PlainPositionalDefault} {id : DeclarationId} {captures : List Lists.Capture}
    {start installed : State} {free : List FreeName} {floor : Nat}
    (target : name ∈ block.owned) (destination : aliasName ∈ block.owned)
    (frame : Body.Frame block free floor installed)
    (result : Nested.SiteResult block name parameters items id captures start (.ok .next installed)) :
    ∃ address saved evaluated,
      Lexical.Evaluates block start items (.ok saved evaluated) ∧
      Body.Evaluates block installed (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
        (.ok (.function address) installed) ∧
      (let copied := installed.write (fileSlot aliasName) (.function address)
       Body.Evaluates block copied (.scalar (.read aliasName)) (Leaf.readOperand (fileSlot aliasName))
          (.ok (.function address) copied) ∧
        copied.heap[address]? = some ⟨.function ⟨id, captures,
          (parameters.optional.map (fileSlot ∘ Prod.fst)).zip saved⟩, false⟩) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.reads_installed_alias_defaults
    target destination frame result

theorem reads_installed_alias {block : LexicalBlock} {name aliasName : String} {parameters : Parameters}
    {items : List PlainPositionalDefault} {id : DeclarationId} {captures : List Lists.Capture}
    {start installed : State} {free : List FreeName} {floor : Nat}
    (target : name ∈ block.owned) (destination : aliasName ∈ block.owned)
    (frame : Body.Frame block free floor installed)
    (result : Nested.SiteResult block name parameters items id captures start (.ok .next installed)) :
    ∃ address saved,
      Body.Evaluates block installed (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
        (.ok (.function address) installed) ∧
      (let copied := installed.write (fileSlot aliasName) (.function address)
       Body.Evaluates block copied (.scalar (.read aliasName)) (Leaf.readOperand (fileSlot aliasName))
          (.ok (.function address) copied) ∧
        copied.heap[address]? = some ⟨.function ⟨id, captures,
          (parameters.optional.map (fileSlot ∘ Prod.fst)).zip saved⟩, false⟩) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.reads_installed_alias
    target destination frame result

/-- A reached successful definition identifies the actual closure and
saved defaults before any subsequent rebind. -/
theorem installation {block : LexicalBlock} {child : Body.Definition} (plan : Nested.Plan block child)
    {id : DeclarationId} {captures : List Lists.Capture} {start installed : State}
    (result : Nested.DefinitionResult plan id captures start (.ok .next installed)) :
    Nonempty (Installed plan id captures installed) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.installation plan result

/-- A subsequent operand that reaches the same function record can use
the independent binder to prepare a checked positional invocation. -/
theorem prepare_installed {block : LexicalBlock} {child : Body.Definition}
    {plan : Nested.Plan block child} {id : DeclarationId} {captures : List Lists.Capture}
    {installed : State} (origin : Installed plan id captures installed)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (found : resolved.program[id]? = some plan.declaration)
    (later : State) (frozen : Bool) (actuals : List Lists.Value)
    (recorded : later.heap[origin.address]? = some ⟨.function ⟨id, captures,
      (child.parameters.optional.map (fileSlot ∘ Prod.fst)).zip origin.values⟩, frozen⟩) :
    let available := List.range resolved.program.size
    ∃ result, Defaults.Binds (child.parameters.slots origin.values) actuals result ∧
      ∃ permitted : id ∈ available,
        prepareExpanded resolved.program available ⟨actuals, []⟩ (.function origin.address) later =
          match result with
          | .error error => .error error later
          | .ok assigned => .ok (.closure ⟨id, permitted, plan.declaration.body⟩)
            (activate later plan.declaration captures assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.prepare_installed
    origin checked found later frozen actuals recorded

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence
