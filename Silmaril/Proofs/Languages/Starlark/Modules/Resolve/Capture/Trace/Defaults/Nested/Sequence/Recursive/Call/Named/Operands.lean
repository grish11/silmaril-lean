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

private theorem resolves_display_operand {block : LexicalBlock} {source code reads}
    (operand : DisplayOperand block source code reads) (initial : List Binding) :
    resolveExpr block.context source initial = .ok (code, reads.reverse ++ initial) := by
  cases operand with
  | plain plain => exact Body.resolves_at plain initial
  | string text => rw [resolveExpr.eq_def]; rfl

private theorem resolves_entries {block : LexicalBlock} {source codes reads}
    (related : DisplayEntries block source codes reads) (initial : List Binding) :
    (source.mapM fun pair : SourceExpr × SourceExpr =>
      StateT.bind (resolveExpr block.context pair.1) fun key =>
        StateT.bind (resolveExpr block.context pair.2) fun value => StateT.pure (key, value)) initial =
      .ok (codes, reads.reverse ++ initial) := by
  induction related generalizing initial with
  | empty => rfl
  | entry key value _ ih =>
    simp [List.mapM_cons, resolves_display_operand key, resolves_display_operand value, ih,
      bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, List.reverse_append, List.append_assoc]

private theorem mapping_resolves {block : LexicalBlock} (mapping : Mapping block) (initial : List Binding) :
    resolveExpr block.context mapping.source initial = .ok (mapping.code, mapping.reads.reverse ++ initial) := by
  have attached :
      (mapping.entries.attach.mapM fun pair =>
        StateT.bind (resolveExpr block.context pair.val.1) fun key =>
          StateT.bind (resolveExpr block.context pair.val.2) fun value => StateT.pure (key, value)) =
      (mapping.entries.mapM fun pair : SourceExpr × SourceExpr =>
        StateT.bind (resolveExpr block.context pair.1) fun key =>
          StateT.bind (resolveExpr block.context pair.2) fun value => StateT.pure (key, value)) := by
    calc
      _ = (mapping.entries.attach.map Subtype.val).mapM (fun pair : SourceExpr × SourceExpr =>
        StateT.bind (resolveExpr block.context pair.1) fun key =>
          StateT.bind (resolveExpr block.context pair.2) fun value => StateT.pure (key, value)) := by
        simp only [List.mapM_map, Function.comp_def]
      _ = _ := by rw [List.attach_map_subtype_val]
  rw [Mapping.source, resolveExpr.eq_def]
  simp only [bind, StateT.bind, pure, StateT.pure]
  rw [attached, resolves_entries mapping.related]
  rfl

theorem mapping_origins {block : LexicalBlock} (mapping : Option (Mapping block)) :
    ∀ binding ∈ mappingReads mapping, ∃ origin, ReadOrigin block binding origin := by
  have operand_origins {source code reads} (operand : DisplayOperand block source code reads) :
      ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin := by
    cases operand with
    | plain plain => exact Body.operand_origins plain
    | string => simp
  have entries_origins {source codes reads} (related : DisplayEntries block source codes reads) :
      ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin := by
    induction related with
    | empty => simp
    | entry key value _ ih =>
      intro binding member
      rcases List.mem_append.mp member with pair | tail
      · exact (List.mem_append.mp pair).elim (operand_origins key binding) (operand_origins value binding)
      · exact ih binding tail
  cases mapping with
  | none => simp [mappingReads]
  | some mapping => exact entries_origins mapping.related

private theorem optional_resolves {α : Type} {block : LexicalBlock}
    (operand : Option α) (source : α → SourceExpr) (code : α → Lowering.Expr) (reads : α → List Binding)
    (resolved : ∀ value initial, resolveExpr block.context (source value) initial =
      .ok (code value, (reads value).reverse ++ initial)) (initial : List Binding) :
    ((operand.map source).mapM (resolveExpr block.context)) initial =
      .ok (operand.map code, ((operand.map reads).getD []).reverse ++ initial) := by
  cases operand with
  | none => rfl
  | some value =>
    simp [Option.mapM, Functor.map, StateT.map, Except.map, resolved]

theorem resolves_at {block : LexicalBlock} {name : String}
    {positional : List SourceExpr} {posCodes : List Lowering.Expr} {posReads : List Binding}
    (slot : Binding) (callee : Body.Operand block (.scalar (.read name)) (Leaf.readOperand slot) [slot])
    (related : Positional block positional posCodes posReads) (keywords : Operands block)
    (star : Option (Spread block) := none) (mapping : Option (Mapping block) := none) :
    resolveTracked block.context
      (.call (.scalar (.read name)) positional keywords.source (star.map Spread.source) (mapping.map Mapping.source)) =
      .ok (expressionAt slot posCodes keywords.codes (star.map Spread.code) (mapping.map Mapping.code),
        slot :: ((posReads ++ keywords.reads) ++ spreadReads star ++ mappingReads mapping)) := by
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
  have starResolved (initial : List Binding) :
      ((star.map Spread.source).mapM (resolveExpr block.context)) initial =
        .ok (star.map Spread.code, (spreadReads star).reverse ++ initial) := by
    have step := optional_resolves star Spread.source Spread.code Spread.reads spread_resolves initial
    cases star <;> exact step
  have mappingResolved := optional_resolves mapping Mapping.source Mapping.code Mapping.reads mapping_resolves
  rw [resolveTracked, resolveExpr.eq_def]
  simp [first, second, Body.resolves_at callee, resolves_positional related, resolves_named keywords.related,
    starResolved, mappingResolved, expressionAt, bind, StateT.bind, Except.bind, pure, StateT.pure,
    Except.pure, Except.map, List.reverse_append, List.append_assoc, mappingReads]

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
  rw [expression, expressionAt, Lowering.Expr.validateCalls.eq_def]
  simp [repeated, throw, bind, Except.bind]
  rfl

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
