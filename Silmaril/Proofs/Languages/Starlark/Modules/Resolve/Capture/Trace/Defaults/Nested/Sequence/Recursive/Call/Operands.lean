module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (resolveTracked resolveExpr)
open Silmaril.Languages.Starlark.Lists (State Outcome Value)
open Silmaril.Languages.Starlark.Lists.Iteration (finishState)

local notation "NormalizedExpr" => Lowering.Resolve.SourceExpr

private theorem resolves_arguments {block : LexicalBlock}
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) (initial : List Binding) :
    (arguments.mapM (resolveExpr block.context)) initial = .ok (codes, reads.reverse ++ initial) := by
  induction related generalizing initial with
  | nil => rfl
  | cons first _ ih =>
    simp [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      Body.resolves_at first, ih, List.reverse_append, List.append_assoc]

theorem resolves {block : LexicalBlock} {name : String}
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (legal : name.toList.head? ≠ some '$') (owned : name ∈ block.owned)
    (related : Arguments block arguments codes reads) :
    resolveTracked block.context (.call (.scalar (.read name)) arguments [] none none) =
      .ok (expression name codes, fileSlot name :: reads) := by
  have callee : Body.Operand block (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) [fileSlot name] :=
    .read legal (.owned owned) (.owned owned)
  have spine : (arguments.attach.mapM fun arg => resolveExpr block.context arg.val) =
      arguments.mapM (resolveExpr block.context) := by
    calc
      _ = (arguments.attach.map Subtype.val).mapM (resolveExpr block.context) := by
        simp only [List.mapM_map, Function.comp_def]
      _ = _ := by rw [List.attach_map_subtype_val]
  rw [resolveTracked, resolveExpr.eq_def]
  simp [spine, Body.resolves_at callee, resolves_arguments related, expression, bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure, Except.map]

theorem keeps_all {first middle last : State}
    (head : Body.Keeps first.heap.size first middle) (tail : Body.Keeps middle.heap.size middle last) :
    Body.Keeps first.heap.size first last := by
  refine ⟨tail.1.trans head.1, ?_⟩
  intro address cell low stored
  have reached := head.2 address cell low stored
  exact tail.2 address cell (Array.getElem?_eq_some_iff.mp reached).choose reached

theorem arguments_total {block : LexicalBlock}
    {arguments : List NormalizedExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Arguments block arguments codes reads) (state : State) :
    ∃ out, Evaluates block state arguments codes out ∧ Body.Keeps state.heap.size state (finishState out) ∧
      (∀ values final, out = .ok values final → values.length = codes.length) := by
  induction related generalizing state with
  | nil => exact ⟨_, .nil, ⟨rfl, fun _ _ _ stored => stored⟩, fun _ _ same => by cases same; rfl⟩
  | cons operand _ ih =>
    obtain ⟨out, first, kept⟩ := Body.operand_total operand state
    cases out with
    | error error final => exact ⟨_, .headError first, kept, fun _ _ impossible => nomatch impossible⟩
    | ok value middle =>
      obtain ⟨tail, later, stable, length⟩ := ih middle
      cases tail with
      | error error final =>
        exact ⟨_, .tailError first later, keeps_all kept stable, fun _ _ impossible => nomatch impossible⟩
      | ok values final =>
        exact ⟨_, .cons first later, keeps_all kept stable, fun _ _ same => by cases same; simp [length _ _ rfl]⟩

theorem evaluates_many (program : Program) (available : List DeclarationId)
    (calls : Lowering.ClosureRuns available)
    {block : LexicalBlock} {state : State} {arguments : List NormalizedExpr} {codes : List Lowering.Expr}
    {out : Outcome (List Value)} (ran : Evaluates block state arguments codes out) :
    Lowering.EvaluatesManyWith program available calls (fun _ => True) state codes out := by
  induction ran with
  | nil => exact .empty
  | cons first _ tail => exact .cons (Body.evaluates_with _ _ _ first) tail
  | headError first => exact .headError (Body.evaluates_with _ _ _ first)
  | tailError first _ tail => exact .tailError (Body.evaluates_with _ _ _ first) tail

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
