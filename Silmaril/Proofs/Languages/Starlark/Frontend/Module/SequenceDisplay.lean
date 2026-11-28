module

public import Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Frontend.Module

open Silmaril.Languages.Starlark
open Functions Functions.Lowering

private theorem sequence_order (evaluate : Expr → Lists.Meaning Lists.Value)
    (allocate : List Lists.Value → Lists.Meaning Lists.Value)
    (elements : List Expr) (state : Lists.State) :
    Lists.Outcome.resume ((elements.attach.mapM fun element => evaluate element.val) state) allocate =
      match (elements.mapM evaluate) state with
      | .ok values next => allocate values next
      | .error error next => .error error next := by
  rw [List.mapM_subtype (g := evaluate) (fun _ _ => rfl), List.unattach_attach]
  simp only [Lists.Outcome.resume]
  cases (elements.mapM evaluate) state <;> rfl

private theorem sequence_cons (evaluate : Expr → Lists.Meaning Lists.Value)
    (allocate : List Lists.Value → Lists.Meaning Lists.Value)
    (first : Expr) (rest : List Expr) (state : Lists.State) :
    (match ((first :: rest).mapM evaluate) state with
    | .ok values next => allocate values next
    | .error error next => .error error next) =
      match evaluate first state with
      | .ok value next =>
        match (rest.mapM evaluate) next with
        | .ok values after => allocate (value :: values) after
        | .error error after => .error error after
      | .error error next => .error error next := by
  rw [List.mapM_cons]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  cases evaluate first state with
  | error _ _ => rfl
  | ok _ next =>
    dsimp only
    cases (rest.mapM evaluate) next <;> rfl

theorem denoteList_order (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (elements : List Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.list elements) state =
      match (elements.mapM (denoteExprWith program available bodyMeaning)) state with
      | .ok values next => Lists.allocate values next
      | .error error next => .error error next := by
  rw [denoteExprWith.eq_2]
  exact sequence_order (denoteExprWith program available bodyMeaning) Lists.allocate elements state

theorem denoteList_cons (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (first : Expr) (rest : List Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.list (first :: rest)) state =
      match denoteExprWith program available bodyMeaning first state with
      | .ok value next =>
        match (rest.mapM (denoteExprWith program available bodyMeaning)) next with
        | .ok values after => Lists.allocate (value :: values) after
        | .error error after => .error error after
      | .error error next => .error error next := by
  rw [denoteList_order]
  exact sequence_cons (denoteExprWith program available bodyMeaning) Lists.allocate first rest state

theorem denoteTuple_order (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (elements : List Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.tuple elements) state =
      match (elements.mapM (denoteExprWith program available bodyMeaning)) state with
      | .ok values next => Lists.allocateTuple values next
      | .error error next => .error error next := by
  rw [denoteExprWith.eq_3]
  exact sequence_order (denoteExprWith program available bodyMeaning) Lists.allocateTuple elements state

theorem denoteTuple_cons (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (first : Expr) (rest : List Expr) (state : Lists.State) :
    denoteExprWith program available bodyMeaning (.tuple (first :: rest)) state =
      match denoteExprWith program available bodyMeaning first state with
      | .ok value next =>
        match (rest.mapM (denoteExprWith program available bodyMeaning)) next with
        | .ok values after => Lists.allocateTuple (value :: values) after
        | .error error after => .error error after
      | .error error next => .error error next := by
  rw [denoteTuple_order]
  exact sequence_cons (denoteExprWith program available bodyMeaning) Lists.allocateTuple first rest state

end Silmaril.Proofs.Languages.Starlark.Frontend.Module
