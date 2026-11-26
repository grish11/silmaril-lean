module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Thms
public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Execution

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call

open Assignment (LexicalBlock)
open Functions
open Functions.Lowering.Resolve (resolveTracked)
open Lists (State Outcome Capture)
local notation "Value" => Lists.Value
open Lists.Iteration (Flow finishState)

local notation "NormalizedExpr" => Lowering.Resolve.SourceExpr

/-- The checked resolver sees the local callee first and the argument reads in order. -/
theorem resolves {block : LexicalBlock} {name : String}
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (legal : name.toList.head? ≠ some '$') (owned : name ∈ block.owned)
    (related : Arguments block arguments codes reads) :
    resolveTracked block.context (.call (.scalar (.read name)) arguments [] none none) =
      .ok (expression name codes, fileSlot name :: reads) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.resolves
    legal owned related

/-- Argument evaluation stops at the first error and keeps existing heap cells. -/
theorem arguments_total {block : LexicalBlock}
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) (state : State) :
    ∃ out, Evaluates block state arguments codes out ∧ Body.Keeps state.heap.size state (finishState out) ∧
      (∀ values final, out = .ok values final → values.length = codes.length) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.arguments_total
    related state

theorem evaluates_many (program : Program) (available : List DeclarationId)
    (calls : Lowering.ClosureRuns available)
    {block : LexicalBlock} {state : State} {arguments : List NormalizedExpr} {codes : List Lowering.Expr}
    {out : Outcome (List Value)} (ran : Evaluates block state arguments codes out) :
    Lowering.EvaluatesManyWith program available calls (fun _ => True) state codes out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.evaluates_many
    program available calls ran

/-- A reached callee error skips every operand and activation. -/
theorem callee_error {parent block : LexicalBlock} (site : Site parent) (id : DeclarationId)
    (program : Program) (available : List DeclarationId) {name : String}
    (owned : name ∈ block.owned) (arguments : List NormalizedExpr) (codes : List Lowering.Expr)
    {state : State} {error : Lists.Error}
    (failed : state.bindingValue (fileSlot name) = .error error) :
    Runs site block id name arguments codes state (.error error state) ∧
      ExecExpr program available state (expression name codes) (.error error state) ∧
      Lowering.denoteExpr program available (expression name codes) state = .error error state :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.callee_error
    site id program available owned arguments codes failed

/-- A source callee read and the record at its evaluated address suffice
for exact checked positional binding and execution of the recursive body. -/
theorem runs {parent block : LexicalBlock} (site : Site parent) {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) :
    ∃ out, Runs site block id name arguments codes state out ∧
      ExecExpr resolved.program available state (expression name codes) out ∧
      Lowering.denoteExpr resolved.program available (expression name codes) state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs
    site profile checked table id found available permitted callee record related

/-- Derive the live call target from a reached definition and an immediate
local copy. Earlier operand allocations survive binding or body failure. -/
theorem runs_installed_alias {parent : LexicalBlock} (site : Site parent)
    {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {defining installed : State} {captures : List Capture}
    (step : Nested.SiteResult parent site.name site.parameters site.defaults id captures defining (.ok .next installed))
    (receipts : Installs defining site.free captures) (cells : Body.CaptureCells defining captures)
    {name : String} (owned : name ∈ parent.owned) (legal : name.toList.head? ≠ some '$')
    {free : List FreeName} {floor : Nat} (frame : Body.Frame parent free floor installed)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments parent arguments codes reads) :
    ∃ address out, Body.Evaluates parent installed (.scalar (.read site.name)) (Leaf.readOperand (fileSlot site.name))
        (.ok (.function address) installed) ∧
      (let copied := installed.write (fileSlot name) (.function address)
       (Lowering.Resolve.resolveTracked parent.context (.call (.scalar (.read name)) arguments [] none none) =
          .ok (expression name codes, fileSlot name :: reads)) ∧
       Runs site parent id name arguments codes copied out ∧
       ExecExpr resolved.program available copied (expression name codes) out ∧
       Lowering.denoteExpr resolved.program available (expression name codes) copied = out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_installed_alias
    site profile checked table id found available permitted step receipts cells owned legal frame related

/-- The alias call keeps its caller's slot map and every cell present before
argument evaluation, on success and on every admitted error. -/
theorem runs_installed_alias_preserving {parent : LexicalBlock} (site : Site parent)
    {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {defining installed : State} {captures : List Capture}
    (step : Nested.SiteResult parent site.name site.parameters site.defaults id captures defining (.ok .next installed))
    (receipts : Installs defining site.free captures) (cells : Body.CaptureCells defining captures)
    {name : String} (owned : name ∈ parent.owned) (legal : name.toList.head? ≠ some '$')
    {free : List FreeName} {floor : Nat} (frame : Body.Frame parent free floor installed)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments parent arguments codes reads) :
    ∃ address out, Body.Evaluates parent installed (.scalar (.read site.name)) (Leaf.readOperand (fileSlot site.name))
        (.ok (.function address) installed) ∧
      (let copied := installed.write (fileSlot name) (.function address)
       (Lowering.Resolve.resolveTracked parent.context (.call (.scalar (.read name)) arguments [] none none) =
          .ok (expression name codes, fileSlot name :: reads)) ∧
       Runs site parent id name arguments codes copied out ∧
       ExecExpr resolved.program available copied (expression name codes) out ∧
       Lowering.denoteExpr resolved.program available (expression name codes) copied = out ∧ Body.Keeps copied.heap.size copied (finishState out)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_installed_alias_preserving
    site profile checked table id found available permitted step receipts cells owned legal frame related

/-- Continue from an independently reached argument result, including an expansion failure. -/
theorem runs_actual {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs)
    (bodyRuns : State → Outcome Flow → Prop)
    (program : Program) (id : DeclarationId) (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site program available id bodyRuns)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    (positional : List Lowering.Expr) (keywords : List (String × Lowering.Expr)) (star starStar : Option Lowering.Expr)
    (actuals : State → Outcome Actual → Prop)
    (reaches : ∀ state, ∃ out, actuals state out ∧
      NativeActuals program available positional keywords star starStar state out ∧
      Body.Keeps state.heap.size state (finishState out))
    {Bound : Type} (binds : BindingRule Bound) (packs : PackRule Bound)
    (total : ∀ defaults actual, ∃ result, binds defaults actual result)
    (prepare : ∀ {reached : State} (closure : ClosureAt site id defining reached address) actual result,
      actuals state (.ok actual reached) → binds closure.defaults actual result →
      match result with
      | .error error => prepareExpanded program available actual (.function address) reached =
          .error error reached
      | .ok bound => ∃ assigned packed, packs reached bound assigned packed ∧
          Body.Keeps reached.heap.size reached packed ∧ packed.bindings = reached.bindings ∧
          prepareExpanded program available actual (.function address) reached =
            .ok (.closure ⟨id, permitted, site.declaration.body⟩)
              (activate packed site.declaration closure.captures assigned)) :
    let code := Lowering.Expr.call (Leaf.readOperand (fileSlot name)) positional keywords star starStar
    ∃ out, RunsActual site bodyRuns block id name actuals binds packs state out ∧
      ExecExpr program available state code out ∧ Lowering.denoteExpr program available code state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_actual
    site bodyRuns program id available permitted enterBody callee record positional keywords star starStar
    actuals reaches binds packs total prepare

theorem runs_packed {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs)
    (bodyRuns : State → Outcome Flow → Prop)
    (program : Program) (id : DeclarationId) (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site program available id bodyRuns)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads)
    (positional : List Lowering.Expr) (keywords : List (String × Lowering.Expr))
    (ordered : positional ++ keywords.map Prod.snd = codes)
    {Bound : Type} (collect : List Value → Actual) (binds : BindingRule Bound) (packs : PackRule Bound)
    (expands : ∀ state values, values.length = codes.length →
      Lowering.Expands ((Lowering.argumentShape positional keywords none none).collect values)
        state (.ok (collect values) state))
    (total : ∀ defaults actual, ∃ result, binds defaults actual result)
    (prepare : ∀ {reached : State} (closure : ClosureAt site id defining reached address) values result,
      binds closure.defaults (collect values) result →
      match result with
      | .error error => prepareExpanded program available (collect values) (.function address) reached =
          .error error reached
      | .ok bound => ∃ assigned packed, packs reached bound assigned packed ∧
          Body.Keeps reached.heap.size reached packed ∧ packed.bindings = reached.bindings ∧
          prepareExpanded program available (collect values) (.function address) reached =
            .ok (.closure ⟨id, permitted, site.declaration.body⟩)
              (activate packed site.declaration closure.captures assigned)) :
    let code := Lowering.Expr.call (Leaf.readOperand (fileSlot name)) positional keywords none none
    ∃ out, RunsPacked site bodyRuns block id name arguments codes collect binds packs state out ∧
      ExecExpr program available state code out ∧ Lowering.denoteExpr program available code state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_packed
    site bodyRuns program id available permitted enterBody callee record related positional keywords ordered
    collect binds packs expands total prepare

/-- A reached local read dispatches through its live closure record. -/
theorem runs_preserving_with {parent block : LexicalBlock} (site : Site parent)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site resolved.program available id bodyRuns)
    {name : String} {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) :
    ∃ out, RunsWith site bodyRuns block id name arguments codes state out ∧
      ExecExpr resolved.program available state (expression name codes) out ∧
      Lowering.denoteExpr resolved.program available (expression name codes) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_preserving_with
    site bodyRuns checked id found available permitted enterBody callee record related

/-- Reuse the guarded alias call with a body derivation at the reduced set. -/
theorem runs_installed_alias_preserving_with {parent : LexicalBlock} (site : Site parent)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved)
    (id : DeclarationId) (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site resolved.program available id bodyRuns)
    {defining installed : State} {captures : List Capture}
    (step : Nested.SiteResult parent site.name site.parameters site.defaults id captures defining (.ok .next installed))
    (receipts : Installs defining site.free captures) (cells : Body.CaptureCells defining captures)
    {name : String} (owned : name ∈ parent.owned) (legal : name.toList.head? ≠ some '$')
    {free : List FreeName} {floor : Nat} (frame : Body.Frame parent free floor installed)
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments parent arguments codes reads) :
    ∃ address out, Body.Evaluates parent installed (.scalar (.read site.name)) (Leaf.readOperand (fileSlot site.name))
        (.ok (.function address) installed) ∧
      (let copied := installed.write (fileSlot name) (.function address)
       (Lowering.Resolve.resolveTracked parent.context (.call (.scalar (.read name)) arguments [] none none) =
          .ok (expression name codes, fileSlot name :: reads)) ∧
       RunsWith site bodyRuns parent id name arguments codes copied out ∧
       ExecExpr resolved.program available copied (expression name codes) out ∧
       Lowering.denoteExpr resolved.program available (expression name codes) copied = out ∧ Body.Keeps copied.heap.size copied (finishState out)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_installed_alias_preserving_with
    site bodyRuns checked id found available permitted enterBody step receipts cells owned legal frame related

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
