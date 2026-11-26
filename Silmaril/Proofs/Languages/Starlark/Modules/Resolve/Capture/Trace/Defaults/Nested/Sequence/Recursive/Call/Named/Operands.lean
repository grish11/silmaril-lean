module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (Arguments)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named hiding Arguments
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (SourceExpr resolveTracked resolveExpr)

local notation "Positional" =>
  Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Arguments
local notation "NamedArgs" =>
  Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Arguments

theorem argument_origins {block : LexicalBlock}
    {source : List (String × SourceExpr)} {codes : List (String × Lowering.Expr)} {reads : List Binding}
    (related : NamedArgs block source codes reads) :
    ∀ binding ∈ reads, ∃ origin, Silmaril.Languages.Starlark.Modules.Resolve.Capture.ReadOrigin block binding origin := by
  induction related with
  | nil => simp
  | cons first _ ih =>
    intro binding member
    exact (List.mem_append.mp member).elim (Body.operand_origins first binding) (ih binding)

private theorem flattened {block : LexicalBlock}
    {source : List (String × SourceExpr)} {codes : List (String × Lowering.Expr)} {reads : List Binding}
    (related : NamedArgs block source codes reads) :
    Positional block (source.map Prod.snd) (codes.map Prod.snd) reads := by
  induction related with
  | nil => exact .nil
  | cons first _ ih => exact .cons first ih

theorem ordered_operands {block : LexicalBlock} {positional : List SourceExpr} {posCodes : List Lowering.Expr}
    {posReads : List Binding} (ordered : Positional block positional posCodes posReads) (keywords : Operands block) :
    Positional block (positional ++ keywords.source.map Prod.snd) (posCodes ++ keywords.codes.map Prod.snd)
      (posReads ++ keywords.reads) := by
  induction ordered with
  | nil => exact flattened keywords.related
  | cons first _ ih => simpa only [List.cons_append, List.append_assoc] using Arguments.cons first ih

theorem names_in_order {block : LexicalBlock}
    {source : List (String × SourceExpr)} {codes : List (String × Lowering.Expr)} {reads : List Binding}
    (related : NamedArgs block source codes reads) : codes.map Prod.fst = source.map Prod.fst := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem resolves_positional {block : LexicalBlock}
    {source : List SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Positional block source codes reads) (initial : List Binding) :
    (source.mapM (resolveExpr block.context)) initial = .ok (codes, reads.reverse ++ initial) := by
  induction related generalizing initial with
  | nil => rfl
  | cons first _ ih =>
    simp [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      Body.resolves_at first, ih, List.reverse_append, List.append_assoc]

private theorem resolves_named {block : LexicalBlock}
    {source : List (String × SourceExpr)} {codes : List (String × Lowering.Expr)} {reads : List Binding}
    (related : NamedArgs block source codes reads) (initial : List Binding) :
    (source.mapM fun arg : String × SourceExpr =>
      StateT.bind (resolveExpr block.context arg.2) fun code => StateT.pure (arg.1, code)) initial =
      .ok (codes, reads.reverse ++ initial) := by
  induction related generalizing initial with
  | nil => rfl
  | cons first _ ih =>
    simp [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      Body.resolves_at first, ih, List.reverse_append, List.append_assoc]

private theorem spread_resolves {block : LexicalBlock} (spread : Spread block) (initial : List Binding) :
    resolveExpr block.context spread.source initial = .ok (spread.code, spread.reads.reverse ++ initial) := by
  have attached {source : List SourceExpr} :
      (source.attach.mapM fun arg => resolveExpr block.context arg.val) =
        source.mapM (resolveExpr block.context) := by
    calc
      _ = (source.attach.map Subtype.val).mapM (resolveExpr block.context) := by
        simp only [List.mapM_map, Function.comp_def]
      _ = _ := by rw [List.attach_map_subtype_val]
  cases spread with
  | list related =>
    rw [Spread.source, resolveExpr.eq_def]
    simp [attached, resolves_positional related, Spread.code, Spread.reads, bind, StateT.bind, Except.bind,
      pure, StateT.pure, Except.pure]
  | tuple related =>
    rw [Spread.source, resolveExpr.eq_def]
    simp [attached, resolves_positional related, Spread.code, Spread.reads, bind, StateT.bind, Except.bind,
      pure, StateT.pure, Except.pure]
  | integer value => exact Body.resolves_at (.int value) initial

theorem spread_origins {block : LexicalBlock} (star : Option (Spread block)) :
    ∀ binding ∈ spreadReads star, ∃ origin, Silmaril.Languages.Starlark.Modules.Resolve.Capture.ReadOrigin block binding origin := by
  have origins {source codes reads} (related : Positional block source codes reads) :
      ∀ binding ∈ reads, ∃ origin, Silmaril.Languages.Starlark.Modules.Resolve.Capture.ReadOrigin block binding origin := by
    induction related with
    | nil => simp
    | cons first _ ih =>
      intro binding member
      exact (List.mem_append.mp member).elim (Body.operand_origins first binding) (ih binding)
  cases star with
  | none => simp [spreadReads]
  | some star =>
    cases star with
    | list related | tuple related => exact origins related
    | integer => simp [spreadReads, Spread.reads]

theorem resolves {block : LexicalBlock} {name : String}
    {positional : List SourceExpr} {posCodes : List Lowering.Expr} {posReads : List Binding}
    (legal : name.toList.head? ≠ some '$') (owned : name ∈ block.owned)
    (related : Positional block positional posCodes posReads) (keywords : Operands block)
    (star : Option (Spread block) := none) :
    resolveTracked block.context (.call (.scalar (.read name)) positional keywords.source (star.map Spread.source) none) =
      .ok (expression name posCodes keywords.codes (star.map Spread.code),
        fileSlot name :: ((posReads ++ keywords.reads) ++ spreadReads star)) := by
  have callee : Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.owned owned) (.owned owned)
  have first : (positional.attach.mapM fun arg => resolveExpr block.context arg.val) =
      positional.mapM (resolveExpr block.context) := by
    calc
      _ = (positional.attach.map Subtype.val).mapM (resolveExpr block.context) := by
        simp only [List.mapM_map, Function.comp_def]
      _ = _ := by rw [List.attach_map_subtype_val]
  have second : (keywords.source.attach.mapM fun arg =>
        StateT.bind (resolveExpr block.context arg.val.2) fun code => StateT.pure (arg.val.1, code)) =
      (keywords.source.mapM fun arg : String × SourceExpr =>
      StateT.bind (resolveExpr block.context arg.2) fun code => StateT.pure (arg.1, code)) := by
    calc
      _ = (keywords.source.attach.map Subtype.val).mapM
          (fun arg : String × SourceExpr =>
      StateT.bind (resolveExpr block.context arg.2) fun code => StateT.pure (arg.1, code)) := by
        simp only [List.mapM_map, Function.comp_def]
      _ = _ := by rw [List.attach_map_subtype_val]
  cases star with
  | none =>
    rw [resolveTracked, resolveExpr.eq_def]
    simp [first, second, Body.resolves_at callee, resolves_positional related, resolves_named keywords.related,
    expression, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Except.map,
      List.reverse_append, spreadReads]
  | some spread =>
    rw [resolveTracked, resolveExpr.eq_def]
    simp [first, second, Body.resolves_at callee, resolves_positional related, resolves_named keywords.related,
      spread_resolves, Option.mapM, expression, bind, StateT.bind, Except.bind, Functor.map, StateT.map, pure, StateT.pure,
      Except.pure, Except.map, List.reverse_append, List.append_assoc, spreadReads]

private theorem no_duplicate {names : List String} (distinct : names.Nodup) : firstDuplicate names = none := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    have separated := List.nodup_cons.mp distinct
    simp [firstDuplicate, separated.1, ih separated.2]

theorem distinct_names {block : LexicalBlock} (keywords : Operands block) :
    firstDuplicate (keywords.codes.map Prod.fst) = none := by
  rw [names_in_order keywords.related]
  exact no_duplicate keywords.distinct

theorem rejects_duplicate (name : String) (positional : List Lowering.Expr)
    (keywords : List (String × Lowering.Expr)) (duplicate : String)
    (repeated : firstDuplicate (keywords.map Prod.fst) = some duplicate) :
    (expression name positional keywords).validateCalls = .error (.duplicateExplicitKeyword duplicate) := by
  rw [expression, Lowering.Expr.validateCalls.eq_def]
  simp [repeated, throw, bind, Except.bind]
  rfl

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
