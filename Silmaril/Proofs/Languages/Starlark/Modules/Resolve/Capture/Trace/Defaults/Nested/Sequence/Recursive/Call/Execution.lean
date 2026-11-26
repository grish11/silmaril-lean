module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Operands
public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call

open Silmaril.Languages.Starlark (Binding Scope)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site Elaborates Emissions)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Value Capture Cell)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

local notation "NormalizedExpr" => Lowering.Resolve.SourceExpr

private theorem positioned {codes : List Lowering.Expr} {values : List Value} (state : State)
    (length : values.length = codes.length) :
    Lowering.Expands ((Lowering.argumentShape codes [] none none).collect values) state (.ok ⟨values, []⟩ state) := by
  have shape : (Lowering.argumentShape codes [] none none).collect values = ⟨values, [], none, none⟩ := by
    simp [Lowering.argumentShape, ArgumentShape.collect, ← length]
  rw [shape]
  simpa only [List.append_nil] using Lowering.Expands.success (args := ⟨values, [], none, none⟩) (keys := [])
    (values := []) (next := state) rfl .empty

private def keep_record {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    {site : Site parent formals varargs kwargs scope} {id : DeclarationId}
    {defining state next : State} {address : Nat} (record : ClosureAt site id defining state address)
    (kept : Body.Keeps state.heap.size state next) : ClosureAt site id defining next address :=
  { record with
    recorded := kept.2 _ _ (Array.getElem?_eq_some_iff.mp record.recorded).choose record.recorded
    live := fun capture present => by
      obtain ⟨value, frozen, found⟩ := record.live capture present
      exact ⟨value, frozen, kept.2 _ _ (Array.getElem?_eq_some_iff.mp found).choose found⟩ }

private abbrev Operational (program : Program) (available : List DeclarationId) :=
  Lowering.EvaluatesWith program available (Lowering.coreClosureRuns program available) (fun _ => True)

private theorem agreement {program : Program} {available : List DeclarationId}
    {state : State} {code : Lowering.Expr} {out : Outcome Value}
    (ran : Operational program available state code out) :
    ExecExpr program available state code out ∧ Lowering.denoteExpr program available code state = out :=
  ⟨.evaluates (fun _ _ _ call => call) ran,
    Lowering.denoteExprWith_eq_of_evaluates (fun _ _ _ call => (exec_iff_denoteBody _ _ _ _ _).mp call) ran⟩

theorem callee_error {parent block : LexicalBlock} (site : Site parent) (id : DeclarationId)
    (program : Program) (available : List DeclarationId) {name : String}
    (owned : name ∈ block.owned) (arguments : List NormalizedExpr) (codes : List Lowering.Expr)
    {state : State} {error : Silmaril.Languages.Starlark.Lists.Error}
    (failed : state.bindingValue (fileSlot name) = .error error) :
    Runs site block id name arguments codes state (.error error state) ∧
      ExecExpr program available state (expression name codes) (.error error state) ∧
      Lowering.denoteExpr program available (expression name codes) state = .error error state := by
  have read : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (state.read (.bound (fileSlot name))) := .read (.owned owned)
  rw [State.read] at read
  simp only [failed] at read
  have native : Operational program available state (expression name codes) (.error error state) := by
    apply Lowering.EvaluatesWith.callError
    simpa only [Lowering.sourceOperands, List.map_nil, Option.toList_none, List.append_nil] using
      Lowering.EvaluatesManyWith.headError (tail := codes) (Body.evaluates_with program available _ read)
  exact ⟨.calleeError read, agreement native⟩

theorem runs_actual_reached {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope)
    (bodyRuns : State → Outcome Flow → Prop)
    (program : Program) (id : DeclarationId) (available : List DeclarationId) (permitted : id ∈ available)
    {name : String} (slot : Binding) {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand slot)
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    (enterReached : ∀ packed, Body.Keeps state.heap.size state packed →
      ∀ assigned : List (Binding × Value),
      let active := activate packed site.declaration record.captures assigned
      ∃ out, bodyRuns active out ∧ Exec program (withoutDeclaration available id) active site.body.code out ∧
        Body.Keeps packed.heap.size packed (finishState (Leaf.returnTo packed out)))
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
    let code := Lowering.Expr.call (Leaf.readOperand slot) positional keywords star starStar
    ∃ out, RunsActual site bodyRuns block id name slot actuals binds packs state out ∧
      ExecExpr program available state code out ∧ Lowering.denoteExpr program available code state = out ∧
      Body.Keeps state.heap.size state (finishState out) := by
  let code := Lowering.Expr.call (Leaf.readOperand slot) positional keywords star starStar
  change ∃ out, RunsActual site bodyRuns block id name slot actuals binds packs state out ∧
    ExecExpr program available state code out ∧ Lowering.denoteExpr program available code state = out ∧
    Body.Keeps state.heap.size state (finishState out)
  let calls := Lowering.coreClosureRuns program available
  have read := Body.evaluates_with program available calls callee
  obtain ⟨args, source, evaluated, kept⟩ := reaches state
  have applyCall {reached : State} {values : List Value} {out : Outcome Value}
      (operands : Lowering.EvaluatesManyWith program available calls (fun _ => True) state
        (Lowering.argumentExprs positional keywords star starStar) (.ok values reached))
      (dispatch : Lowering.AppliesWith program available calls (Lowering.argumentShape positional keywords star starStar)
        reached (.function address :: values) out) :
      Operational program available state code out := by
    dsimp [code]
    apply Lowering.EvaluatesWith.call
    · simpa only [Lowering.sourceOperands, Lowering.argumentExprs] using
        Lowering.EvaluatesManyWith.cons read operands
    · exact dispatch
  cases args with
  | error error residual =>
    have native : Operational program available state code (.error error residual) := by
      cases evaluated with
      | operandError operands =>
        dsimp [code]
        apply Lowering.EvaluatesWith.callError
        simpa only [Lowering.sourceOperands, Lowering.argumentExprs] using
          Lowering.EvaluatesManyWith.tailError read operands
      | expanded operands expansion =>
        exact applyCall operands (.expansionError expansion)
    exact ⟨_, .argumentError callee source, (agreement native).1, (agreement native).2, kept⟩
  | ok actual actualState =>
    have invoke {out : Outcome Value}
        (dispatch : Lowering.DispatchesWith program available calls actualState (.function address) actual out) :
        Operational program available state code out := by
      cases evaluated with
      | expanded operands expansion => exact applyCall operands (.expanded expansion dispatch)
    let reached := keep_record record kept
    obtain ⟨bound, binding⟩ := total reached.defaults actual
    have ready := prepare reached actual bound source binding
    cases bound with
    | error error =>
      have ⟨native, meaning⟩ := agreement (invoke (.reject ready))
      exact ⟨_, .bindingError callee source reached binding, native, meaning, kept⟩
    | ok bound =>
      obtain ⟨assigned, packed, packedArgs, packedKept, sameBindings, ready⟩ := ready
      obtain ⟨out, bodyRun, executable, restored⟩ :=
        enterReached packed (keeps_all kept packedKept) assigned
      have sameCaller : Leaf.returnTo packed out = Leaf.returnTo actualState out := by
        cases out <;> simp [Leaf.returnTo, restoreCaller, packedKept.1, sameBindings, finishState]
      have dispatch : Lowering.DispatchesWith program available calls actualState (.function address)
          actual (Leaf.returnTo actualState out) := by
        cases out with
        | ok flow final => exact .returned ready executable
        | error error final => exact .failed ready executable
      have ⟨native, meaning⟩ := agreement (invoke dispatch)
      exact ⟨_, .invoked callee source reached binding packedArgs (show bodyRuns (activate packed site.declaration reached.captures assigned) out from bodyRun), native, meaning,
        sameCaller ▸ keeps_all (keeps_all kept packedKept) restored⟩

theorem runs_actual {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope)
    (bodyRuns : State → Outcome Flow → Prop)
    (program : Program) (id : DeclarationId) (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site program available id bodyRuns)
    {name : String} (slot : Binding) {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand slot)
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
    let code := Lowering.Expr.call (Leaf.readOperand slot) positional keywords star starStar
    ∃ out, RunsActual site bodyRuns block id name slot actuals binds packs state out ∧
      ExecExpr program available state code out ∧ Lowering.denoteExpr program available code state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  runs_actual_reached site bodyRuns program id available permitted slot callee record
    (fun packed preserved assigned =>
      enterBody packed defining record.captures record.installed
        (fun capture member => by
          obtain ⟨value, frozen, found⟩ := record.live capture member
          exact ⟨value, frozen, preserved.2 _ _ (Array.getElem?_eq_some_iff.mp found).choose found⟩) assigned) positional keywords star starStar actuals reaches binds packs total prepare

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
      Body.Keeps state.heap.size state (finishState out) := by
  refine runs_actual site bodyRuns program id available permitted enterBody (fileSlot name) callee record positional keywords none none _
    (fun reached => ?_) binds packs total ?_
  · obtain ⟨out, ran, kept, length⟩ := arguments_total related reached
    have native := evaluates_many program available (Lowering.coreClosureRuns program available) ran
    have nativeOrdered : Lowering.EvaluatesManyWith program available (Lowering.coreClosureRuns program available)
        (fun _ => True) reached (Lowering.argumentExprs positional keywords none none) out := by
      simpa only [Lowering.argumentExprs, Option.toList_none, List.append_nil, ordered] using native
    cases out with
    | error error residual => exact ⟨_, .operandError ran, .operandError nativeOrdered, kept⟩
    | ok values final =>
      exact ⟨_, .expanded ran rfl, .expanded nativeOrdered (expands final values (length _ _ rfl)), kept⟩
  · intro reached closure actual result assembled binding
    cases assembled with
    | expanded _ collected =>
      cases collected
      exact prepare closure _ result binding

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
      Body.Keeps state.heap.size state (finishState out) := by
  apply runs_packed site bodyRuns resolved.program id available permitted enterBody callee record related
    codes [] (by simp) (fun values => ⟨values, []⟩)
    (fun defaults actual => Binds (site.parameters.slots defaults) actual.positional) Unpacked
  · exact fun state _ length => positioned state length
  · exact fun defaults actual =>
      Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.binds_total
        (site.parameters.slots defaults) actual.positional
  · intro reachedState reached actual result binding
    -- The positional profile always collects an empty keyword list.
    have codeLength : (site.defaults.map PlainPositionalDefault.value).length = site.parameters.optional.length := by
      simpa using congrArg List.length (Lexical.translates site.lexical).1
    have ready := Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.checked_prepare_positional
      checked id available permitted site.parameters site.declaration _ found rfl codeLength reachedState
      address reached.frozen reached.captures reached.defaults actual reached.length reached.recorded binding
    cases result with
    | error => exact ready
    | ok assigned => exact ⟨assigned, reachedState, ⟨rfl, rfl⟩, ⟨rfl, fun _ _ _ h => h⟩, rfl, ready⟩

private theorem recursive_entry {parent : LexicalBlock} (site : Site parent)
    {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block site.source seed site.body final emissions)
    (program : Program) (table : PreservesDeclarations final program) (available : List DeclarationId) (id : DeclarationId) :
    BodyEntry site program available id (fun state out =>
      Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Runs
        site.block state site.source site.body.code out) := by
  intro caller defining captures installed live assigned
  obtain ⟨out, source, _, native, _, restored⟩ :=
    Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.runs_activated
      site profile program table (withoutDeclaration available id) caller defining captures installed live assigned
  exact ⟨out, source, native, restored.1, fun address cell _ stored => restored.2.2 address cell stored⟩

theorem runs_preserving {parent block : LexicalBlock} (site : Site parent) {seed final : Program} {emissions : Emissions}
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
      Lowering.denoteExpr resolved.program available (expression name codes) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  runs_preserving_with site _ checked id found available permitted
    (recursive_entry site profile resolved.program table available id) callee record related

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
      Lowering.denoteExpr resolved.program available (expression name codes) state = out := by
  obtain ⟨out, source, native, meaning, _⟩ :=
    runs_preserving site profile checked table id found available permitted callee record related
  exact ⟨out, source, native, meaning⟩

private theorem installed_cells {parent : LexicalBlock} (site : Site parent)
    {id : DeclarationId} {defining installed : State} {captures : List Capture}
    (step : Nested.SiteResult parent site.name site.parameters site.defaults id captures defining (.ok .next installed))
    (cells : Body.CaptureCells defining captures) : Body.CaptureCells installed captures := by
  cases step with
  | @installed saved next evaluated ran exactState _ _ =>
    rw [exactState]
    let record : Cell := ⟨.function ⟨id, captures,
      (site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip saved⟩, false⟩
    let grown : State := { evaluated with heap := evaluated.heap.push record }
    have kept := Lexical.evaluates_keeps site.lexical ran
    have live : Body.CaptureCells grown captures := by
      intro capture member
      obtain ⟨value, frozen, found⟩ := cells capture member
      have reached : evaluated.heap[capture.address]? = some ⟨.binding value, frozen⟩ :=
        kept.2 _ _ (Array.getElem?_eq_some_iff.mp found).choose found
      have within := (Array.getElem?_eq_some_iff.mp reached).choose
      exact ⟨value, frozen, by simp [grown, Array.getElem?_push, Nat.ne_of_lt within, reached]⟩
    exact Body.capture_cells_written grown (fileSlot site.name) (.function evaluated.heap.size) live

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
       Lowering.denoteExpr resolved.program available (expression name codes) copied = out ∧ Body.Keeps copied.heap.size copied (finishState out)) := by
  obtain ⟨address, saved, evaluated, evaluatedDefaults, first, read, exactRecord⟩ :=
    Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.reads_installed_alias_defaults
      site.target owned frame step
  let origin : ClosureAt site id defining (installed.write (fileSlot name) (.function address)) address :=
    ⟨captures, saved, false, Lexical.evaluated_length site.lexical evaluatedDefaults, exactRecord, receipts,
      Body.capture_cells_written installed (fileSlot name) (.function address) (installed_cells site step cells)⟩
  obtain ⟨out, ran, operated, denoted, kept⟩ :=
    runs_preserving_with site bodyRuns checked id found available permitted enterBody read origin related
  exact ⟨address, out, first, resolves legal owned related, ran, operated, denoted, kept⟩

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
  runs_installed_alias_preserving_with site _ checked id found available permitted
    (recursive_entry site profile resolved.program table available id) step receipts cells owned legal frame related

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
       Lowering.denoteExpr resolved.program available (expression name codes) copied = out) := by
  obtain ⟨address, out, first, translated, ran, native, meaning, _⟩ :=
    runs_installed_alias_preserving site profile checked table id found available permitted step receipts cells owned legal frame related
  exact ⟨address, out, first, translated, ran, native, meaning⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
