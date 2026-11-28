module

public import Silmaril.Languages.Starlark.Denotation.Defs
public import Silmaril.Languages.Starlark.Operational.Defs
import Silmaril.Languages.Starlark.Binary64.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark

open Silmaril.Languages.Starlark

private theorem orderedCompare_eq_of_orders {lhs rhs : Value} {order : Option Ordering}
    (ran : ScalarOrders lhs rhs order) : lhs.orderedCompare rhs = order := by
  cases ran with
  | integers order => exact congrArg some ((Binary64.orders_iff_compareNumbers _ _ _).mp order)
  | intFloat decoded order | floatInt decoded order =>
    simpa only [Value.orderedCompare, (Binary64.decodes_iff_decode _ _).mp decoded] using
      congrArg some ((Binary64.orders_iff_compareNumbers _ _ _).mp order)
  | floats left right order =>
    simpa only [Value.orderedCompare, (Binary64.decodes_iff_decode _ _).mp left,
      (Binary64.decodes_iff_decode _ _).mp right] using
      congrArg some ((Binary64.orders_iff_compareNumbers _ _ _).mp order)
  | booleans => rfl
  | unavailable excluded => cases lhs <;> cases rhs <;> simp_all [OrderableTogether, Value.orderedCompare]

private theorem orders_orderedCompare (lhs rhs : Value) : ScalarOrders lhs rhs (lhs.orderedCompare rhs) := by
  have ordered (a b : Binary64.Number) : Binary64.Orders a b (Binary64.compareNumbers a b) :=
    (Binary64.orders_iff_compareNumbers _ _ _).mpr rfl
  have decoded (bits : UInt64) : Binary64.Decodes bits (Binary64.decode bits) :=
    (Binary64.decodes_iff_decode _ _).mpr rfl
  cases lhs <;> cases rhs <;> first
  | exact .unavailable (by simp [OrderableTogether])
  | exact .booleans _ _
  | exact .integers (ordered _ _)
  | exact .intFloat (decoded _) (ordered _ _)
  | exact .floatInt (decoded _) (ordered _ _)
  | exact .floats (decoded _) (decoded _) (ordered _ _)

private theorem applyBinary_comparison {op : BinaryOp} (comparison : op.isComparison = true)
    (lhs rhs : Value) : applyBinary op lhs rhs = comparisonResult op lhs rhs (lhs.orderedCompare rhs) := by
  cases op <;> first | rfl | cases comparison

private theorem answer_iff_result (op : BinaryOp) (lhs rhs : Value) (order : Option Ordering)
    (out : Result Value) : ComparisonAnswer op lhs rhs order out ↔ comparisonResult op lhs rhs order = out := by
  cases op <;> cases order <;> first
  | rfl
  | rename_i order; cases order <;> rfl
  | cases lhs <;> cases rhs <;> rfl

theorem compares_iff_applyBinary (op : BinaryOp) (lhs rhs : Value) (out : Result Value) :
    Compares op lhs rhs out ↔ op.isComparison = true ∧ applyBinary op lhs rhs = out := by
  constructor
  · intro ran
    cases ran with
    | result comparison ordered answer =>
      refine ⟨comparison, ?_⟩
      rw [applyBinary_comparison comparison, orderedCompare_eq_of_orders ordered]
      exact (answer_iff_result _ _ _ _ _).mp answer
  · rintro ⟨comparison, result⟩
    rw [← result, applyBinary_comparison comparison]
    exact .result comparison (orders_orderedCompare lhs rhs) ((answer_iff_result _ _ _ _ _).mpr rfl)

theorem denoteExpr_eq_of_eval {frame : Frame} {expr : ResolvedExpr} {result : Result Value}
    (h : Eval frame expr result) : denoteExpr expr frame = result := by
  induction h <;>
    (try have applied := ((compares_iff_applyBinary _ _ _ _).mp (by assumption)).2) <;>
    simp_all [denoteExpr, bind, Except.bind]

theorem denoteStmt_eq_of_exec {frame : Frame} {stmt : ResolvedStmt} {result : Result Completion}
    (h : Exec frame stmt result) : denoteStmt stmt frame = result := by
  induction h <;> (try have hExpr := denoteExpr_eq_of_eval (by assumption)) <;>
    simp_all [denoteStmt, bind, Except.bind] <;> rfl

theorem eval_denoteExpr (expr : ResolvedExpr) (frame : Frame) :
    Eval frame expr (denoteExpr expr frame) := by
  induction expr with
  | int => exact .int
  | read => exact .read
  | unary op arg ih =>
    cases h : denoteExpr arg frame with
    | error error => simpa [denoteExpr, h, bind, Except.bind] using Eval.unaryError (op := op) (h ▸ ih)
    | ok value => simpa [denoteExpr, h, bind, Except.bind] using Eval.unary (op := op) (h ▸ ih)
  | binary op left right ihLeft ihRight =>
    cases hl : denoteExpr left frame with
    | error error =>
      simpa [denoteExpr, hl, bind, Except.bind] using
        Eval.binaryLeftError (op := op) (right := right) (hl ▸ ihLeft)
    | ok lhs =>
      cases hr : denoteExpr right frame with
      | error error =>
        simpa [denoteExpr, hl, hr, bind, Except.bind] using Eval.binaryRightError (op := op) (hl ▸ ihLeft) (hr ▸ ihRight)
      | ok rhs =>
        by_cases comparison : op.isComparison = true
        · have ran := (compares_iff_applyBinary op lhs rhs _).mpr ⟨comparison, rfl⟩
          simpa [denoteExpr, hl, hr, bind, Except.bind] using
            Eval.comparison (hl ▸ ihLeft) (hr ▸ ihRight) ran
        · have arithmetic : op.isComparison = false := by simpa only [Bool.not_eq_true] using comparison
          simpa [denoteExpr, hl, hr, bind, Except.bind] using
            Eval.binary (op := op) (hl ▸ ihLeft) (hr ▸ ihRight) arithmetic
  | logical op left right ihLeft ihRight =>
    cases hl : denoteExpr left frame with
    | error error =>
      simpa [denoteExpr, hl, bind, Except.bind] using
        Eval.logicalError (op := op) (right := right) (hl ▸ ihLeft)
    | ok lhs =>
      cases h : op.runsRight lhs with
      | false =>
        simpa [denoteExpr, hl, h, bind, Except.bind] using Eval.logicalShort (right := right) (hl ▸ ihLeft) h
      | true =>
        simpa [denoteExpr, hl, h, bind, Except.bind] using Eval.logicalRight (hl ▸ ihLeft) h ihRight
  | conditional test yes no ihTest ihYes ihNo =>
    cases ht : denoteExpr test frame with
    | error error =>
      simpa [denoteExpr, ht, bind, Except.bind] using Eval.conditionalError (yes := yes) (no := no) (ht ▸ ihTest)
    | ok value =>
      cases h : value.truth with
      | false =>
        simpa [denoteExpr, ht, h, bind, Except.bind] using Eval.conditionalFalse (yes := yes) (ht ▸ ihTest) h ihNo
      | true =>
        simpa [denoteExpr, ht, h, bind, Except.bind] using Eval.conditionalTrue (no := no) (ht ▸ ihTest) h ihYes

theorem exec_denoteStmt (stmt : ResolvedStmt) (frame : Frame) :
    Exec frame stmt (denoteStmt stmt frame) := by
  induction stmt generalizing frame with
  | pass => exact .pass
  | eval expr =>
    cases h : denoteExpr expr frame with
    | error error =>
      rw [denoteStmt, h]
      exact .evalError (h ▸ eval_denoteExpr expr frame)
    | ok value =>
      rw [denoteStmt, h]
      exact .eval (h ▸ eval_denoteExpr expr frame)
  | assign name rhs =>
    cases h : denoteExpr rhs frame with
    | error error =>
      rw [denoteStmt, h]
      exact .assignError (h ▸ eval_denoteExpr rhs frame)
    | ok value =>
      rw [denoteStmt, h]
      exact .assign (h ▸ eval_denoteExpr rhs frame)
  | seq first rest ihFirst ihRest =>
    cases h : denoteStmt first frame with
    | error error =>
      rw [denoteStmt, h]
      exact .seqError (h ▸ ihFirst frame)
    | ok result =>
      obtain ⟨next, returned⟩ := result
      cases returned with
      | none =>
        rw [denoteStmt, h]
        exact .seqNext (h ▸ ihFirst frame) (ihRest next)
      | some value =>
        rw [denoteStmt, h]
        exact .seqReturn (h ▸ ihFirst frame)
  | branch test yes no ihYes ihNo =>
    cases ht : denoteExpr test frame with
    | error error =>
      rw [denoteStmt, ht]
      exact .branchError (ht ▸ eval_denoteExpr test frame)
    | ok value =>
      have hTest : Eval frame test (.ok value) := ht ▸ eval_denoteExpr test frame
      cases h : value.truth with
      | false =>
        simpa [denoteStmt, ht, h, bind, Except.bind] using Exec.branchFalse (yes := yes) hTest h (ihNo frame)
      | true =>
        simpa [denoteStmt, ht, h, bind, Except.bind] using Exec.branchTrue (no := no) hTest h (ihYes frame)
  | ret value =>
    cases value with
    | none => exact .retNone
    | some expr =>
      cases h : denoteExpr expr frame with
      | error error =>
        rw [denoteStmt, h]
        exact .retError (h ▸ eval_denoteExpr expr frame)
      | ok value =>
        rw [denoteStmt, h]
        exact .retSome (h ▸ eval_denoteExpr expr frame)

end Silmaril.Proofs.Languages.Starlark
