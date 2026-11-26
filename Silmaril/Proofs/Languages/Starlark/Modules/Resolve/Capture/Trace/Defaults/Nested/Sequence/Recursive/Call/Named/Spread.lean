module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Operands

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named hiding Arguments
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Value Cell listElements tupleElements projectCell getCell)
open Silmaril.Languages.Starlark.Lists.Iteration (finishState)

private abbrev Many (program : Program) (available : List DeclarationId) :=
  Lowering.EvaluatesManyWith program available (Lowering.coreClosureRuns program available) (fun _ => True)

private theorem append_error {program available state codes error final}
    (ran : Many program available state codes (.error error final)) (tail : List Lowering.Expr) :
    Many program available state (codes ++ tail) (.error error final) := by
  cases ran with
  | headError first => exact .headError first
  | tailError first later => exact .tailError first (append_error later tail)
termination_by codes.length

private theorem append_success {program available state codes values reached}
    (ran : Many program available state codes (.ok values reached))
    {tail out} (later : Many program available reached tail out) :
    Many program available state (codes ++ tail) (out.resume fun extra final => .ok (values ++ extra) final) := by
  cases ran with
  | empty => cases out <;> exact later
  | cons first rest =>
    cases out with
    | error => exact .tailError first (append_success rest later)
    | ok => exact .cons first (append_success rest later)
termination_by codes.length

private theorem shape {positional : List Lowering.Expr} {keywords : List (String × Lowering.Expr)}
    {star : Option Lowering.Expr} {values : List Value} {spread : Option Value}
    (complete : values.length = (positional ++ keywords.map Prod.snd).length)
    (present : spread.isSome = star.isSome) :
    (Lowering.argumentShape positional keywords star none).collect (values ++ spread.toList) =
      ⟨values.take positional.length, (keywords.map Prod.fst).zip (values.drop positional.length), spread, none⟩ := by
  simp only [List.length_append, List.length_map] at complete
  have before : positional.length ≤ values.length := by omega
  have length : (values.drop positional.length).length = (keywords.map Prod.fst).length := by
    simp only [List.length_drop, List.length_map]
    omega
  have named : (keywords.map Prod.fst).zip (values.drop positional.length ++ spread.toList) =
      (keywords.map Prod.fst).zip (values.drop positional.length) := by
    simpa using (List.zip_append (l₁ := keywords.map Prod.fst) (r₁ := [])
      (l₂ := values.drop positional.length) (r₂ := spread.toList) length.symm)
  have after : (values.drop positional.length ++ spread.toList).drop (keywords.map Prod.fst).length =
      spread.toList := by rw [← length, List.drop_append_length]
  simp only [Lowering.argumentShape, ArgumentShape.collect, List.take_append_of_le_length before,
    List.drop_append_of_le_length before, after, named]
  cases star <;> cases spread <;> simp_all

private inductive NativeSpread (program : Program) (available : List DeclarationId)
    (code : Option Lowering.Expr) (state : State) : Outcome (List Value) → Prop where
  | operandError {error final} :
      Many program available state code.toList (.error error final) →
      NativeSpread program available code state (.error error final)
  | expanded {spread : Option Value} {reached out} :
      Many program available state code.toList (.ok spread.toList reached) →
      spread.isSome = code.isSome →
      Lowering.ExpandsStar reached spread out →
      NativeSpread program available code state out

private theorem keeps_push (state : State) (cell : Cell) :
    Body.Keeps state.heap.size state {state with heap := state.heap.push cell} := by
  refine ⟨by simp, fun address _ below stored => ?_⟩
  simp [Array.getElem?_push, Nat.ne_of_lt below, stored]

private theorem keeps_after {first middle final : State}
    (earlier : Body.Keeps first.heap.size first middle) (later : Body.Keeps middle.heap.size middle final) :
    Body.Keeps first.heap.size first final :=
  ⟨later.1.trans earlier.1, fun address cell below stored =>
    let present := earlier.2 address cell below stored
    later.2 address cell (Array.getElem?_eq_some_iff.mp present).choose present⟩

private theorem spread_total (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} (star : Option (Spread block)) (state : State) :
    ∃ out, Spreads block star state out ∧ NativeSpread program available (star.map Spread.code) state out ∧
      Body.Keeps state.heap.size state (finishState out) := by
  let calls := Lowering.coreClosureRuns program available
  cases star with
  | none =>
    exact ⟨_, .absent _, .expanded (spread := none) .empty rfl .empty, ⟨rfl, fun _ _ _ h => h⟩⟩
  | some operand =>
    cases operand with
    | integer n =>
      let value : Value := .scalar (.int n)
      have read : Many program available state [Lowering.Expr.atom (.scalar (.int n))] (.ok [value] state) :=
        .cons (.atom trivial .scalar) .empty
      exact ⟨_, .invalid _ _, .expanded (spread := some value) read rfl (.invalid (by simp [value, Builtins.IsCollection])),
        ⟨rfl, fun _ _ _ h => h⟩⟩
    | list related =>
      obtain ⟨out, source, retained, _⟩ := arguments_total related state
      have native := evaluates_many program available calls source
      cases out with
      | error error final => exact ⟨_, .list source, .operandError (.headError (.list native)), retained⟩
      | ok values reached =>
        let cell : Cell := ⟨.list values, false⟩
        let allocated : State := {reached with heap := reached.heap.push cell}
        let value : Value := .list reached.heap.size
        have loaded : listElements reached.heap.size allocated = .ok values allocated := by
          simp [listElements, projectCell, getCell, bind, EStateM.bind, pure, EStateM.pure, allocated, cell]
        have expansion : Lowering.ExpandsStar allocated (some value) (.ok values allocated) := by
          simpa only [loaded] using Lowering.ExpandsStar.list (state := allocated) reached.heap.size
        exact ⟨_, .list source, .expanded (spread := some value) (.cons (.list native) .empty) rfl expansion,
          keeps_after retained (keeps_push reached cell)⟩
    | tuple related =>
      obtain ⟨out, source, retained, _⟩ := arguments_total related state
      have native := evaluates_many program available calls source
      cases out with
      | error error final => exact ⟨_, .tuple source, .operandError (.headError (.tuple native)), retained⟩
      | ok values reached =>
        let key := (values.mapM fun value => (reached.keyOf value).toOption).map
          (fun parts => .openTuple :: parts.flatten ++ [.closeTuple])
        let cell : Cell := ⟨.tuple values key, false⟩
        let allocated : State := {reached with heap := reached.heap.push cell}
        let value : Value := .tuple reached.heap.size
        have loaded : tupleElements reached.heap.size allocated = .ok values allocated := by
          simp [tupleElements, projectCell, getCell, bind, EStateM.bind, pure, EStateM.pure, allocated, cell]
        have expansion : Lowering.ExpandsStar allocated (some value) (.ok values allocated) := by
          simpa only [loaded] using Lowering.ExpandsStar.tuple (state := allocated) reached.heap.size
        exact ⟨_, .tuple source, .expanded (spread := some value) (.cons (.tuple native) .empty) rfl expansion,
          keeps_after retained (keeps_push reached cell)⟩

theorem actuals_total (program : Program) (available : List DeclarationId) {block : LexicalBlock}
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) (keywords : Operands block)
    (star : Option (Spread block)) (state : State) :
    ∃ out, Actuals block (arguments ++ keywords.source.map Prod.snd) (codes ++ keywords.codes.map Prod.snd)
        codes.length (keywords.codes.map Prod.fst) star state out ∧
      NativeActuals program available codes keywords.codes (star.map Spread.code) state out ∧
      Body.Keeps state.heap.size state (finishState out) := by
  let calls := Lowering.coreClosureRuns program available
  obtain ⟨out, source, kept, length⟩ := arguments_total (ordered_operands related keywords) state
  have explicit := evaluates_many program available calls source
  cases out with
  | error error final =>
    exact ⟨_, .operandError source, .operandError (by
      simpa only [Lowering.argumentExprs, Option.toList_none, List.append_nil] using
        append_error explicit (star.map Spread.code).toList), kept⟩
  | ok values reached =>
    obtain ⟨spread, spliced, native, retained⟩ := spread_total program available star reached
    have together := keeps_after kept retained
    cases native with
    | operandError rejected =>
      exact ⟨_, .spreadError source spliced, .operandError (by
        simpa only [Lowering.argumentExprs, Option.toList_none, List.append_nil, Outcome.resume] using
          append_success explicit rejected), together⟩
    | @expanded value expandedState _ evaluated present transport =>
      have assembled : Many program available state
          (Lowering.argumentExprs codes keywords.codes (star.map Spread.code) none)
          (.ok (values ++ value.toList) expandedState) := by
        simpa only [Lowering.argumentExprs, Option.toList_none, List.append_nil, Outcome.resume] using
          append_success explicit evaluated
      have shape := shape (length _ _ rfl) present
      cases spread with
      | error error final =>
        refine ⟨_, .spreadError source spliced, .expanded assembled ?_, together⟩
        rw [shape]
        exact .spreadError (keys := []) rfl transport
      | ok elements final =>
        refine ⟨_, .expanded source spliced, .expanded assembled ?_, together⟩
        rw [shape]
        simpa only [collect, List.append_nil] using Lowering.Expands.success (keys := []) rfl transport

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
