module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Defs

public import Silmaril.Languages.Starlark.Functions.Lowering.Source.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call

open Assignment (LexicalBlock)
open Functions
open Lists (State Outcome)
open Lists.Iteration (Flow finishState)

local notation "NormalizedExpr" => Lowering.Resolve.SourceExpr

local notation "Value" => Lists.Value

/-- Elaborate each positional operand in the caller's lexical block. -/
inductive Arguments (block : LexicalBlock) :
    List NormalizedExpr → List Lowering.Expr → List Binding → Prop where
  | nil : Arguments block [] [] []
  | cons {source : NormalizedExpr} {code : Lowering.Expr} {reads restReads : List Binding}
      {rest : List NormalizedExpr} {codes : List Lowering.Expr} :
      Body.Operand block source code reads → Arguments block rest codes restReads →
      Arguments block (source :: rest) (code :: codes) (reads ++ restReads)

/-- Evaluate the positional operands in order and stop at the first error. -/
inductive Evaluates (block : LexicalBlock) :
    State → List NormalizedExpr → List Lowering.Expr → Outcome (List Value) → Prop where
  | nil {state : State} : Evaluates block state [] [] (.ok [] state)
  | cons {state middle final : State} {source : NormalizedExpr} {code : Lowering.Expr} {value : Value}
      {rest : List NormalizedExpr} {codes : List Lowering.Expr} {values : List Value} :
      Body.Evaluates block state source code (.ok value middle) →
      Evaluates block middle rest codes (.ok values final) →
      Evaluates block state (source :: rest) (code :: codes) (.ok (value :: values) final)
  | headError {state final : State} {source : NormalizedExpr} {code : Lowering.Expr} {error : Lists.Error}
      {rest : List NormalizedExpr} {codes : List Lowering.Expr} :
      Body.Evaluates block state source code (.error error final) →
      Evaluates block state (source :: rest) (code :: codes) (.error error final)
  | tailError {state middle final : State} {source : NormalizedExpr} {code : Lowering.Expr} {value : Value}
      {rest : List NormalizedExpr} {codes : List Lowering.Expr} {error : Lists.Error} :
      Body.Evaluates block state source code (.ok value middle) →
      Evaluates block middle rest codes (.error error final) →
      Evaluates block state (source :: rest) (code :: codes) (.error error final)

@[expose] def expression (name : String) (arguments : List Lowering.Expr) : Lowering.Expr :=
  .call (Leaf.readOperand (fileSlot name)) arguments [] none none

/-- Evidence for the actual record reached at a function value. The
defining frame supplies the addresses and the current heap supplies the
live cells and still-stored default values. -/
structure ClosureAt {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent keywords varargs kwargs)
    (id : DeclarationId) (defining state : State) (address : Nat) where
  captures : List Lists.Capture
  defaults : List Value
  frozen : Bool
  length : defaults.length = site.defaultSources.length
  recorded : state.heap[address]? = some ⟨.function ⟨id, captures,
    site.defaultKeys.zip defaults⟩, frozen⟩
  installed : Installs defining site.free captures
  live : Body.CaptureCells state captures

/-- The body proof operates at the callee's reduced declaration set. -/
abbrev BodyEntry {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent keywords varargs kwargs) (program : Program)
    (available : List DeclarationId) (id : DeclarationId) (bodyRuns : State → Outcome Flow → Prop) : Prop :=
  ∀ (caller defining : State) (captures : List Lists.Capture), Installs defining site.free captures →
    Body.CaptureCells caller captures → ∀ (assigned : List (Binding × Lists.Value)),
    let active := activate caller site.declaration captures assigned
    ∃ out, bodyRuns active out ∧ Exec program (withoutDeclaration available id) active site.body.code out ∧
      Body.Keeps caller.heap.size caller (finishState (Leaf.returnTo caller out))

abbrev BindingRule (Bound : Type) := List Value → Actual → Except Lists.Error Bound → Prop

abbrev PackRule (Bound : Type) := State → Bound → List (Binding × Value) → State → Prop

abbrev Unpacked : PackRule (List (Binding × Value)) :=
  fun caller bound assigned packed => assigned = bound ∧ packed = caller

/-- All operands must succeed before expansion. An operand error skips expansion. -/
inductive ReachesActual {Operands : Type} (operands : State → Outcome Operands → Prop)
    (expand : State → Operands → Outcome Actual → Prop) : State → Outcome Actual → Prop where
  | operandError {state final : State} {error : Lists.Error} :
      operands state (.error error final) → ReachesActual operands expand state (.error error final)
  | expanded {state reached : State} {values : Operands} {out : Outcome Actual} :
      operands state (.ok values reached) → expand reached values out → ReachesActual operands expand state out

abbrev NativeActuals (program : Program) (available : List DeclarationId) (positional : List Lowering.Expr)
    (keywords : List (String × Lowering.Expr)) (star starStar : Option Lowering.Expr) :=
  ReachesActual
    (fun state => Lowering.EvaluatesManyWith program available (Lowering.coreClosureRuns program available)
      (fun _ => True) state (Lowering.argumentExprs positional keywords star starStar))
    (fun reached values =>
      Lowering.Expands ((Lowering.argumentShape positional keywords star starStar).collect values) reached)

/-- A call reads the callee before the argument phase. Only a successful
argument phase can reach binding, packing and activation. -/
inductive RunsActual {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent keywords varargs kwargs) (bodyRuns : State → Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (callee : String)
    {Bound : Type} (actuals : State → Outcome Actual → Prop) (binds : BindingRule Bound) (packs : PackRule Bound) :
    State → Outcome Value → Prop where
  | calleeError {state next : State} {error : Lists.Error} :
      Body.Evaluates block state (.scalar (.read callee)) (Leaf.readOperand (fileSlot callee)) (.error error next) →
      RunsActual site bodyRuns block id callee actuals binds packs state (.error error next)
  | argumentError {state next : State} {address : Nat} {error : Lists.Error} :
      Body.Evaluates block state (.scalar (.read callee)) (Leaf.readOperand (fileSlot callee)) (.ok (.function address) state) →
      actuals state (.error error next) →
      RunsActual site bodyRuns block id callee actuals binds packs state (.error error next)
  | bindingError {state actualState defining : State} {address : Nat} {actual : Actual} {error : Lists.Error} :
      Body.Evaluates block state (.scalar (.read callee)) (Leaf.readOperand (fileSlot callee)) (.ok (.function address) state) →
      actuals state (.ok actual actualState) →
      (record : ClosureAt site id defining actualState address) →
      binds record.defaults actual (.error error) →
      RunsActual site bodyRuns block id callee actuals binds packs state (.error error actualState)
  | invoked {state actualState defining packed : State} {address : Nat} {actual : Actual} {bodyOut : Outcome Flow}
      {bound : Bound} {assigned : List (Binding × Value)} :
      Body.Evaluates block state (.scalar (.read callee)) (Leaf.readOperand (fileSlot callee)) (.ok (.function address) state) →
      actuals state (.ok actual actualState) →
      (record : ClosureAt site id defining actualState address) →
      binds record.defaults actual (.ok bound) →
      packs actualState bound assigned packed →
      bodyRuns (activate packed site.declaration record.captures assigned) bodyOut →
      RunsActual site bodyRuns block id callee actuals binds packs state (Leaf.returnTo actualState bodyOut)

abbrev RunsPacked {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent keywords varargs kwargs) (bodyRuns : State → Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (callee : String) (arguments : List NormalizedExpr)
    (codes : List Lowering.Expr) {Bound : Type} (collect : List Value → Actual)
    (binds : BindingRule Bound) (packs : PackRule Bound) :=
  RunsActual site bodyRuns block id callee
    (ReachesActual (fun state => Evaluates block state arguments codes)
      (fun reached values out => out = .ok (collect values) reached)) binds packs

abbrev RunsWith {parent : LexicalBlock} (site : Site parent) (bodyRuns : State → Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (callee : String)
    (arguments : List NormalizedExpr) (codes : List Lowering.Expr) :=
  RunsPacked site bodyRuns block id callee arguments codes (fun values => ⟨values, []⟩)
    (fun defaults actual => Binds (site.parameters.slots defaults) actual.positional) Unpacked

abbrev Runs {parent : LexicalBlock} (site : Site parent) :=
  RunsWith site (fun state out => Sequence.Runs site.block state site.source site.body.code out)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
