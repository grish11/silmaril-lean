module

public import Silmaril.Languages.Starlark.Comparison.Operational.Defs

public section

namespace Silmaril.Languages.Starlark

/-- Big-step evaluation with explicit failure and short-circuit rules. -/
inductive Eval (frame : Frame) : ResolvedExpr → Result Value → Prop where
  | int {n : Int} : Eval frame (.int n) (.ok (.int n))
  | read {ref : Ref} : Eval frame (.read ref) (frame.read ref)
  | unary {op : UnaryOp} {arg : ResolvedExpr} {a : Value} :
      Eval frame arg (.ok a) → Eval frame (.unary op arg) (applyUnary op a)
  | unaryError {op : UnaryOp} {arg : ResolvedExpr} {error : RuntimeError} :
      Eval frame arg (.error error) → Eval frame (.unary op arg) (.error error)
  | binary {op : BinaryOp} {left right : ResolvedExpr} {a b : Value} :
      Eval frame left (.ok a) → Eval frame right (.ok b) →
      op.isComparison = false →
      Eval frame (.binary op left right) (applyBinary op a b)
  | comparison {op : BinaryOp} {left right : ResolvedExpr} {a b : Value} {out : Result Value} :
      Eval frame left (.ok a) → Eval frame right (.ok b) → Compares op a b out →
      Eval frame (.binary op left right) out
  | binaryLeftError {op : BinaryOp} {left right : ResolvedExpr} {error : RuntimeError} :
      Eval frame left (.error error) → Eval frame (.binary op left right) (.error error)
  | binaryRightError {op : BinaryOp} {left right : ResolvedExpr} {a : Value} {error : RuntimeError} :
      Eval frame left (.ok a) → Eval frame right (.error error) →
      Eval frame (.binary op left right) (.error error)
  | logicalShort {op : LogicalOp} {left right : ResolvedExpr} {a : Value} :
      Eval frame left (.ok a) → op.runsRight a = false →
      Eval frame (.logical op left right) (.ok a)
  | logicalRight {op : LogicalOp} {left right : ResolvedExpr} {a : Value} {result : Result Value} :
      Eval frame left (.ok a) → op.runsRight a = true → Eval frame right result →
      Eval frame (.logical op left right) result
  | logicalError {op : LogicalOp} {left right : ResolvedExpr} {error : RuntimeError} :
      Eval frame left (.error error) → Eval frame (.logical op left right) (.error error)
  | conditionalTrue {test yes no : ResolvedExpr} {a : Value} {result : Result Value} :
      Eval frame test (.ok a) → a.truth = true → Eval frame yes result →
      Eval frame (.conditional test yes no) result
  | conditionalFalse {test yes no : ResolvedExpr} {a : Value} {result : Result Value} :
      Eval frame test (.ok a) → a.truth = false → Eval frame no result →
      Eval frame (.conditional test yes no) result
  | conditionalError {test yes no : ResolvedExpr} {error : RuntimeError} :
      Eval frame test (.error error) → Eval frame (.conditional test yes no) (.error error)

/-- Big-step execution with a separate return signal and no rule for resuming after failure. -/
inductive Exec : Frame → ResolvedStmt → Result Completion → Prop where
  | pass {frame : Frame} : Exec frame .pass (.ok ⟨frame, none⟩)
  | eval {frame : Frame} {expr : ResolvedExpr} {a : Value} :
      Eval frame expr (.ok a) → Exec frame (.eval expr) (.ok ⟨frame, none⟩)
  | evalError {frame : Frame} {expr : ResolvedExpr} {error : RuntimeError} :
      Eval frame expr (.error error) → Exec frame (.eval expr) (.error error)
  | assign {frame : Frame} {expr : ResolvedExpr} {name : Binding} {a : Value} :
      Eval frame expr (.ok a) → Exec frame (.assign name expr) (.ok ⟨frame.write name a, none⟩)
  | assignError {frame : Frame} {expr : ResolvedExpr} {name : Binding} {error : RuntimeError} :
      Eval frame expr (.error error) → Exec frame (.assign name expr) (.error error)
  | seqNext {frame next : Frame} {first rest : ResolvedStmt} {result : Result Completion} :
      Exec frame first (.ok ⟨next, none⟩) → Exec next rest result →
      Exec frame (.seq first rest) result
  | seqReturn {frame next : Frame} {first rest : ResolvedStmt} {a : Value} :
      Exec frame first (.ok ⟨next, some a⟩) →
      Exec frame (.seq first rest) (.ok ⟨next, some a⟩)
  | seqError {frame : Frame} {first rest : ResolvedStmt} {error : RuntimeError} :
      Exec frame first (.error error) → Exec frame (.seq first rest) (.error error)
  | branchTrue {frame : Frame} {test : ResolvedExpr} {yes no : ResolvedStmt}
      {a : Value} {result : Result Completion} :
      Eval frame test (.ok a) → a.truth = true → Exec frame yes result →
      Exec frame (.branch test yes no) result
  | branchFalse {frame : Frame} {test : ResolvedExpr} {yes no : ResolvedStmt}
      {a : Value} {result : Result Completion} :
      Eval frame test (.ok a) → a.truth = false → Exec frame no result →
      Exec frame (.branch test yes no) result
  | branchError {frame : Frame} {test : ResolvedExpr} {yes no : ResolvedStmt}
      {error : RuntimeError} :
      Eval frame test (.error error) → Exec frame (.branch test yes no) (.error error)
  | retNone {frame : Frame} : Exec frame (.ret none) (.ok ⟨frame, some .none⟩)
  | retSome {frame : Frame} {expr : ResolvedExpr} {a : Value} :
      Eval frame expr (.ok a) → Exec frame (.ret (some expr)) (.ok ⟨frame, some a⟩)
  | retError {frame : Frame} {expr : ResolvedExpr} {error : RuntimeError} :
      Eval frame expr (.error error) → Exec frame (.ret (some expr)) (.error error)

end Silmaril.Languages.Starlark
