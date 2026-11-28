module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Operands
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Mapping

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named hiding Arguments
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Value Cell listElements tupleElements)
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
    {star mapping : Option Lowering.Expr} {values : List Value} {spread : Option Value} {dict : Option Nat}
    (complete : values.length = (positional ++ keywords.map Prod.snd).length)
    (present : spread.isSome = star.isSome) (mapped : dict.isSome = mapping.isSome) :
    (Lowering.argumentShape positional keywords star mapping).collect (values ++ spread.toList ++ (dict.map Value.dict).toList) =
      ⟨values.take positional.length, (keywords.map Prod.fst).zip (values.drop positional.length),
        spread, dict.map Value.dict⟩ := by
  simp only [List.length_append, List.length_map] at complete
  have before : positional.length ≤ values.length := by omega
  have length : (values.drop positional.length).length = (keywords.map Prod.fst).length := by
    simp only [List.length_drop, List.length_map]
    omega
  let tail := spread.toList ++ (dict.map Value.dict).toList
  have named : (keywords.map Prod.fst).zip (values.drop positional.length ++ tail) =
      (keywords.map Prod.fst).zip (values.drop positional.length) := by
    simpa using (List.zip_append (l₁ := keywords.map Prod.fst) (r₁ := [])
      (l₂ := values.drop positional.length) (r₂ := tail) length.symm)
  have after : (values.drop positional.length ++ tail).drop (keywords.map Prod.fst).length =
      tail := by rw [← length, List.drop_append_length]
  rw [List.append_assoc]
  change (Lowering.argumentShape positional keywords star mapping).collect (values ++ tail) = _
  simp only [Lowering.argumentShape, ArgumentShape.collect, List.take_append_of_le_length before,
    List.drop_append_of_le_length before, after, named]
  cases star <;> cases spread <;> cases mapping <;> cases dict <;> simp_all [tail]

private inductive SpreadValue : Option Value → Prop where
  | absent : SpreadValue none
  | list (address : Nat) : SpreadValue (some (.list address))
  | tuple (address : Nat) : SpreadValue (some (.tuple address))
  | integer (value : Int) : SpreadValue (some (.scalar (.int value)))

private theorem spread_total (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} (star : Option (Spread block)) (state : State) :
    ∃ out, EvaluatesSpread block star state out ∧
      Many program available state (star.map Spread.code).toList
        (out.resume fun value reached => .ok value.toList reached) ∧
      Body.Keeps state.heap.size state (finishState out) ∧
      (∀ value reached, out = .ok value reached → SpreadValue value ∧ value.isSome = star.isSome) := by
  let calls := Lowering.coreClosureRuns program available
  cases star with
  | none =>
    exact ⟨_, .absent _, .empty, ⟨rfl, fun _ _ _ h => h⟩, fun _ _ h => by cases h; exact ⟨.absent, rfl⟩⟩
  | some operand =>
    cases operand with
    | integer n =>
      exact ⟨_, .integer _ _, .cons (.atom trivial .scalar) .empty,
        ⟨rfl, fun _ _ _ h => h⟩, fun _ _ h => by cases h; exact ⟨.integer _, rfl⟩⟩
    | list related =>
      obtain ⟨out, source, retained, _⟩ := arguments_total related state
      have native := evaluates_many program available calls source
      cases out with
      | error error final => exact ⟨_, .list source, .headError (.list native), retained, fun _ _ h => nomatch h⟩
      | ok values reached =>
        exact ⟨_, .list source, .cons (.list native) .empty,
          keeps_after retained (keeps_push reached ⟨.list values, false⟩),
          fun _ _ h => by cases h; exact ⟨.list _, rfl⟩⟩
    | tuple related =>
      obtain ⟨out, source, retained, _⟩ := arguments_total related state
      have native := evaluates_many program available calls source
      cases out with
      | error error final => exact ⟨_, .tuple source, .headError (.tuple native), retained, fun _ _ h => nomatch h⟩
      | ok values reached =>
        let key := (values.mapM fun value => (reached.keyOf value).toOption).map
          (fun parts => .openTuple :: parts.flatten ++ [.closeTuple])
        exact ⟨_, .tuple source, .cons (.tuple native) .empty,
          keeps_after retained (keeps_push reached ⟨.tuple values key, false⟩),
          fun _ _ h => by cases h; exact ⟨.tuple _, rfl⟩⟩

private theorem expand_positional_total {value : Option Value} (supported : SpreadValue value) (state : State) :
    ∃ out, ExpandsPositionals state value out ∧ Lowering.ExpandsStar state value out ∧ finishState out = state := by
  cases supported with
  | absent => exact ⟨_, .absent, .empty, rfl⟩
  | integer n => exact ⟨_, .invalid n, .invalid (by simp [Builtins.IsCollection]), rfl⟩
  | list address => exact ⟨_, .list address, .list address, project_state state address _⟩
  | tuple address => exact ⟨_, .tuple address, .tuple address, project_state state address _⟩

private theorem expand_total (positional : Nat) (keywords : List String) (values : OperandValues)
    (supported : SpreadValue values.star) (state : State) :
    ∃ out, ExpandsActuals positional keywords state values out ∧
      Lowering.Expands ⟨values.explicit.take positional, keywords.zip (values.explicit.drop positional),
        values.star, values.mapping.map Value.dict⟩ state out ∧ finishState out = state := by
  obtain ⟨out, mapping, mapped, kept⟩ := expand_mapping_total state values.mapping
  cases out with
  | error error final => exact ⟨_, .badMapping mapping, .mappingError mapped, kept⟩
  | ok named reached =>
    obtain ⟨out, spread, spliced, retained⟩ := expand_positional_total supported reached
    cases out with
    | error error final => exact ⟨_, .badPositionals mapping spread, .spreadError mapped spliced, retained.trans kept⟩
    | ok elements final => exact ⟨_, .ready mapping spread, .success mapped spliced, retained.trans kept⟩

theorem actuals_total (program : Program) (available : List DeclarationId) {block : LexicalBlock}
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) (keywords : Operands block)
    (star : Option (Spread block)) (mapping : Option (Mapping block)) (state : State) :
    ∃ out, Actuals block (arguments ++ keywords.source.map Prod.snd) (codes ++ keywords.codes.map Prod.snd)
        codes.length (keywords.codes.map Prod.fst) star mapping state out ∧
      NativeActuals program available codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code) state out ∧
      Body.Keeps state.heap.size state (finishState out) := by
  let calls := Lowering.coreClosureRuns program available
  obtain ⟨out, source, kept, length⟩ := arguments_total (ordered_operands related keywords) state
  have explicit := evaluates_many program available calls source
  cases out with
  | error error final =>
    exact ⟨_, .operandError (.explicitError source), .operandError (by
      simpa only [Lowering.argumentExprs, List.append_assoc] using
        append_error explicit ((star.map Spread.code).toList ++ (mapping.map Mapping.code).toList)), kept⟩
  | ok values reached =>
    obtain ⟨out, spliced, starExec, retained, shapeStar⟩ := spread_total program available star reached
    have retained := keeps_after kept retained
    cases out with
    | error error final =>
      exact ⟨_, .operandError (.starError source spliced), .operandError
        (append_error (append_success explicit starExec) (mapping.map Mapping.code).toList), retained⟩
    | ok spread middle =>
      have prior := append_success explicit starExec
      obtain ⟨out, dict, mapExec, keptMap, present⟩ := mapping_total program available mapping middle
      have kept := keeps_after retained keptMap
      cases out with
      | error error final =>
        exact ⟨_, .operandError (.mappingError source spliced dict), .operandError (append_success prior mapExec), kept⟩
      | ok address final =>
        obtain ⟨supported, starPresent⟩ := shapeStar _ _ rfl
        have assembled : Many program available state
            (Lowering.argumentExprs codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code))
            (.ok (values ++ spread.toList ++ (address.map Value.dict).toList) final) :=
          append_success prior mapExec
        obtain ⟨result, expanded, native, unchanged⟩ :=
          expand_total codes.length (keywords.codes.map Prod.fst) ⟨values, spread, address⟩ supported final
        refine ⟨result, .expanded (.ready source spliced dict) expanded, .expanded assembled ?_, unchanged.symm ▸ kept⟩
        rw [shape (length _ _ rfl) (by simpa using starPresent) (by simpa using present _ _ rfl)]
        exact native

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
