module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Dispatch

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall

open Block (ModuleBinders)
open Assignment (InOrder)
open Functions
open Lists (State Address Capture Outcome)
open Lists.Iteration (Flow)

local notation "NormalizedExpr" => Functions.Lowering.Resolve.SourceExpr
local notation "ResolvedExpr" => Functions.Lowering.Expr

/-- Each checked normalized command contributes one resolved command. -/
theorem checked_command_count {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) :
    resolved.source.commands.length = commands.length :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_command_count checked

/-- The whole emitted chain retains its table entries after checked module compilation. -/
theorem checked_chain_site (before after : List Command) (chain : Forwarding.Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain) (suffixProfile : Segment globals after) :
    ∃ seed head frames, Forwarding.Emits globals [] chain (head :: frames) ∧ Forwarding.Links seed chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name (Forwarding.EmittedProgram seed frames).size)) ∧
      (∀ (index : Nat) (declaration : Functions.Declaration), (Forwarding.EmittedProgram seed (head :: frames))[index]? = some declaration →
        resolved.program[index]? = some declaration) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_chain_site
    before after chain globals linked resolved binders checked accepted suffixProfile

/-- The checked site links the whole chain and records the leaf's actual lexical block. -/
theorem checked_definition_site (before after : List Command) (chain : Forwarding.Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain) (suffixProfile : Segment globals after) :
    ∃ seed head frames, Forwarding.Emits globals [] chain (head :: frames) ∧ Forwarding.Links seed chain (head :: frames) ∧
      Forwarding.ScopedLeaves globals [] chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name (Forwarding.EmittedProgram seed frames).size)) ∧
      (∀ (index : Nat) (declaration : Functions.Declaration), (Forwarding.EmittedProgram seed (head :: frames))[index]? = some declaration →
        resolved.program[index]? = some declaration) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_chain_scoped_site
    before after chain globals linked resolved binders checked accepted suffixProfile

/-- The checked site links the whole chain and records the leaf's actual lexical block. -/
theorem checked_chain_scoped_site (after : List Command) (chain : Forwarding.Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (.define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (.define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain) (suffixProfile : Segment globals after) :
    ∃ seed head frames, Forwarding.Emits globals [] chain (head :: frames) ∧ Forwarding.Links seed chain (head :: frames) ∧
      Forwarding.ScopedLeaves globals [] chain (head :: frames) ∧
      resolved.source.commands[0]? = some (.exec (.define chain.name (Forwarding.EmittedProgram seed frames).size)) ∧
      (∀ (index : Nat) (declaration : Functions.Declaration), (Forwarding.EmittedProgram seed (head :: frames))[index]? = some declaration →
        resolved.program[index]? = some declaration) :=
  checked_definition_site
    [] after chain globals linked resolved binders checked accepted suffixProfile

/-- A definition that appends one declaration keeps its emitted index
through later checked commands. -/
theorem checked_single_emission (before after : List Command) (command : Command) (name : String)
    (globals : List String) (linked : Program) (resolved : ResolvedModule) (declaration : Declaration)
    (binders : ModuleBinders (before ++ command :: after) globals)
    (checked : resolve (before ++ command :: after) linked = .ok resolved)
    (suffix : Segment globals after)
    (emits : ∀ program, elaborateCommand ⟨⟨[], globals⟩, .global⟩ command program =
      .ok (.exec (.define name program.size), program.push declaration)) :
    ∃ id, resolved.source.commands[before.length]? = some (.exec (.define name id)) ∧
      resolved.program[id]? = some declaration :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_single_emission
    before after command name globals linked resolved declaration binders checked suffix emits

/-- A successful operand resolution identifies the checked assignment at its source position. -/
theorem checked_assign_site (before after : List Command) (destination : String)
    (source : NormalizedExpr) (code : ResolvedExpr) (reads : List Binding)
    (globals : List String) (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .assign destination source :: after) globals)
    (checked : resolve (before ++ .assign destination source :: after) linked = .ok resolved)
    (operand : Lowering.Resolve.resolveTracked ⟨[], globals⟩ source = .ok (code, reads)) :
    resolved.source.commands[before.length]? = some (.exec (.assignExpr destination code)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_assign_site
    before after destination source code reads globals linked resolved binders checked operand

/-- The source command position identifies the root definition and its
actual declaration table entry after compiling the suffix. -/
theorem checked_root_site (before after : List Command) (chain : Forwarding.Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain) (suffixProfile : Segment globals after) :
    ∃ head frames id, Forwarding.Emits globals [] chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name id)) ∧
      resolved.program[id]? = some head.declaration :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_root_site
    before after chain globals linked resolved binders checked accepted suffixProfile

/-- The intervening name assignments occupy their corresponding
segment of the compiled command list. -/
theorem checked_writes_site (before after : List Command) {source : List Command}
    {code : List Modules.Command} {globals : List String} {name : String}
    {state final : Lists.State} (writes : Writes globals name state source code final)
    {linked : Program} {resolved : ResolvedModule} (binders : ModuleBinders (before ++ source ++ after) globals)
    (checked : resolve (before ++ source ++ after) linked = .ok resolved) :
    ∃ earlier later, earlier.length = before.length ∧ resolved.source.commands = earlier ++ code ++ later :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_writes_site
    before after writes binders checked

theorem operand_total {globals : List String} {source : NormalizedExpr} {code : ResolvedExpr}
    (related : Operand globals source code) (state : State) :
    ∃ out, Evaluates state source out ∧ Lists.Iteration.finishState out = state :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.operand_total related state

/-- Admitted operands produce ordered values or the reached operand
error in the same state. -/
theorem operands_total {globals : List String} {source : List NormalizedExpr} {resolved : List ResolvedExpr}
    (related : InOrder (Operand globals) source resolved) (state : State) :
    (∃ values, EvaluatesOperands state source (.ok values state)) ∨
      ∃ error, EvaluatesOperands state source (.error error state) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.operands_total
    related state

/-- Entering a module gives distinct owned addresses. -/
theorem enter_distinct (source : Modules.Source) (caller : State) : DistinctOwned (enter source caller) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.enter_distinct source caller

/-- Function activation allocates distinct owned binding cells. -/
theorem activation_distinct (caller : State) (declaration : Declaration)
    (captures : List Capture) (assigned : List (Binding × Lists.Value)) :
    DistinctOwned (activate caller declaration captures assigned) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.activation_distinct caller declaration captures assigned

theorem write_other_cell (state : State) (binding : Binding) (value : Lists.Value) (address : Address)
    (other : state.slots binding ≠ some (.owned address)) :
    (state.write binding value).heap[address]? = state.heap[address]? :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.write_other_cell state binding value address other

/-- Writing a different name preserves the live closure and its binding. -/
theorem write_keeps_live (state : State) (name destination : String) (value : Lists.Value)
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool} {defaults : List (Binding × Lists.Value)}
    (distinct : DistinctOwned state) (live : Live state name address id captures frozen defaults)
    (unrelated : destination ≠ name) :
    DistinctOwned (state.write (globalSlot destination) value) ∧
      Live (state.write (globalSlot destination) value) name address id captures frozen defaults :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.write_keeps_live state name destination value
    distinct live unrelated

/-- Successful intervening assignments run with exactly the source
state and preserve the callee binding and closure cell. -/
theorem writes_run_and_keep (program : Program) (host : Catalog)
    {globals : List String} {name : String} {state final : State}
    {source : List Command} {code : List Modules.Command}
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool}
    (writes : Writes globals name state source code final)
    (distinct : DistinctOwned state) (live : Live state name address id captures frozen) :
    Modules.Runs program host state code (.ok () final) ∧
      DistinctOwned final ∧ Live final name address id captures frozen :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.writes_run_and_keep
    program host writes distinct live

/-- A normalized evaluation command containing an admitted positional
call emits the corresponding resolved call at its command position. -/
theorem checked_call_site (before after : List Command) (callee : NormalizedExpr) (positional : List NormalizedExpr)
    (function : ResolvedExpr) (actuals : List ResolvedExpr) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .eval (.call callee positional [] none none) :: after) globals)
    (checked : resolve (before ++ .eval (.call callee positional [] none none) :: after) linked = .ok resolved)
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals) :
    resolved.source.commands[before.length]? = some (.exec (.evalExpr (.call function actuals [] none none))) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_call_site
    before after callee positional function actuals globals linked resolved binders checked related arguments

/-- The actual declaration ID from the checked source site supplies
the entry definition step and its live callee. The step starts in the
fresh module frame. -/
theorem checked_root_setup (before after : List Command) (chain : Forwarding.Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Forwarding.Accepted globals program [] chain) (suffixProfile : Segment globals after)
    (caller : State) :
    let initial := enter resolved.source caller
    ∃ head frames id next captures, Forwarding.Emits globals [] chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name id)) ∧
      resolved.program[id]? = some head.declaration ∧
      Exec resolved.program (List.range resolved.program.size) initial (.define (globalSlot chain.name) id) (.ok .next next) ∧
      DistinctOwned next ∧ Live next chain.name initial.heap.size id captures false :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_root_setup
    before after chain globals linked resolved binders checked accepted suffixProfile caller

/-- The first reached operand error exits the call with its exact
state before expansion, binding, or dispatch. -/
theorem operand_error (program : Program) (available : List DeclarationId) {globals : List String}
    {state next : State} {callee : NormalizedExpr} {positional : List NormalizedExpr}
    {function : ResolvedExpr} {actuals : List ResolvedExpr} {error : Lists.Error}
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals)
    (evaluated : EvaluatesOperands state (callee :: positional) (.error error next)) :
    Exec program available state (.evalExpr (.call function actuals [] none none)) (.error error next) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.operand_error
    program available related arguments evaluated

/-- A reached operand error can also be used before an enclosing write. -/
theorem operand_error_expr (program : Program) (available : List DeclarationId) {globals : List String}
    {state next : State} {callee : NormalizedExpr} {positional : List NormalizedExpr}
    {function : ResolvedExpr} {actuals : List ResolvedExpr} {error : Lists.Error}
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals)
    (evaluated : EvaluatesOperands state (callee :: positional) (.error error next)) :
    ExecExpr program available state (.call function actuals [] none none) (.error error next) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.operand_error_expr
    program available related arguments evaluated

/-- After source operand evaluation succeeds, the independent
positional binder determines arity failure or the exact activation.
The callee-body premise uses the reduced declaration set. -/
theorem checked_invocation {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} {name : String} {state : State} {positional : List NormalizedExpr} {actuals : List ResolvedExpr}
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool} {frame : Forwarding.Frame}
    {values : List Lists.Value} (checked : resolve commands linked = .ok resolved)
    (callee : Operand globals (.scalar (.read name)) (.atom (.read (.bound (globalSlot name)))))
    (arguments : InOrder (Operand globals) positional actuals)
    (live : Live state name address id captures frozen) (found : resolved.program[id]? = some frame.declaration)
    (evaluated : EvaluatesOperands state positional (.ok values state)) :
    ∃ result, Entry.Binds frame.parameters values result ∧
      ∀ (out : Outcome Flow),
        (∀ assigned, result = .ok assigned →
          Exec resolved.program (withoutDeclaration (List.range resolved.program.size) id)
            (activate state frame.declaration captures assigned) frame.code out) →
        Exec resolved.program (List.range resolved.program.size) state
          (.evalExpr (.call (.atom (.read (.bound (globalSlot name)))) actuals [] none none))
          (match result with
          | .error error => .error error state
          | .ok _ => completeCall state none out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_invocation
    checked callee arguments live found evaluated

/-- The assignment form preserves the call at its checked source position. -/
theorem checked_call_assignment_site (before after : List Command) (destination : String) (callee : NormalizedExpr) (positional : List NormalizedExpr)
    (function : ResolvedExpr) (actuals : List ResolvedExpr) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .assign destination (.call callee positional [] none none) :: after) globals)
    (checked : resolve (before ++ .assign destination (.call callee positional [] none none) :: after) linked = .ok resolved)
    (related : Operand globals callee function) (arguments : InOrder (Operand globals) positional actuals) :
    resolved.source.commands[before.length]? = some (.exec (.assignExpr destination (.call function actuals [] none none))) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_call_assignment_site
    before after destination callee positional function actuals globals linked resolved binders checked related arguments

/-- A checked call expression retains its value for the enclosing assignment.
Binding and body execution use the supplied exact rules. -/
theorem checked_invocation_expr {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} {name : String} {state : State} {positional : List NormalizedExpr} {actuals : List ResolvedExpr}
    {address : Address} {id : Nat} {captures : List Capture} {frozen : Bool} {frame : Forwarding.Frame}
    {values : List Lists.Value} (checked : resolve commands linked = .ok resolved)
    (callee : Operand globals (.scalar (.read name)) (.atom (.read (.bound (globalSlot name)))))
    (arguments : InOrder (Operand globals) positional actuals)
    (binding : state.bindingValue (globalSlot name) = .ok (.function address))
    (cell : state.heap[address]? = some ⟨.function ⟨id, captures, []⟩, frozen⟩)
    (found : resolved.program[id]? = some frame.declaration)
    (evaluated : EvaluatesOperands state positional (.ok values state))
    {result : Except Lists.Error (List (Binding × Lists.Value))}
    (binds : Entry.Binds frame.parameters values result) (out : Outcome Flow)
    (bodyRun : ∀ assigned, result = .ok assigned →
      Exec resolved.program (withoutDeclaration (List.range resolved.program.size) id)
        (activate state frame.declaration captures assigned) frame.code out) :
    ExecExpr resolved.program (List.range resolved.program.size) state
      (.call (.atom (.read (.bound (globalSlot name)))) actuals [] none none)
      (match result with
      | .error error => .error error state
      | .ok _ => match out with
        | .ok flow final => .ok (Lowering.callValue flow) (restoreCaller state final)
        | .error error final => .error error (restoreCaller state final)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.checked_invocation_expr
    checked callee arguments binding cell found evaluated binds out bodyRun

theorem resolves_operand {globals : List String} {source : NormalizedExpr} {code : ResolvedExpr}
    (related : Operand globals source code) :
    ∃ reads, Lowering.Resolve.resolveTracked ⟨[], globals⟩ source = .ok (code, reads) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.resolves_operand related

theorem resolves_display {globals : List String} {items : List NormalizedExpr} {codes : List ResolvedExpr}
    (related : InOrder (Operand globals) items codes) :
    ∃ reads, Lowering.Resolve.resolveTracked ⟨[], globals⟩ (.list items) = .ok (.list codes, reads) ∧
      Lowering.Resolve.resolveTracked ⟨[], globals⟩ (.tuple items) = .ok (.tuple codes, reads) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.resolves_display related

theorem evaluates_operand (program : Program) (available : List DeclarationId) (calls : Lowering.ClosureRuns available)
    {globals : List String} {state : State} {source : NormalizedExpr} {code : ResolvedExpr} {out : Outcome Lists.Value}
    (related : Operand globals source code) (evaluated : Evaluates state source out) :
    Lowering.EvaluatesWith program available calls (fun _ => True) state code out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.evaluates_operand
    program available calls related evaluated

theorem evaluates_operands (program : Program) (available : List DeclarationId) (calls : Lowering.ClosureRuns available)
    {globals : List String} {state : State} {source : List NormalizedExpr} {codes : List ResolvedExpr}
    {out : Outcome (List Lists.Value)} (related : InOrder (Operand globals) source codes)
    (evaluated : EvaluatesOperands state source out) :
    Lowering.EvaluatesManyWith program available calls (fun _ => True) state codes out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.evaluates_operands
    program available calls related evaluated

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall
