module

public import Silmaril.Languages.Starlark.Denotation.Defs
public import Silmaril.Languages.Starlark.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Soundness

public section

namespace Silmaril.Languages.Starlark

/-- The independent scalar comparison rules determine the exact result or type error. -/
theorem compares_iff_applyBinary (op : BinaryOp) (lhs rhs : Value) (out : Result Value) :
    Compares op lhs rhs out ↔ op.isComparison = true ∧ applyBinary op lhs rhs = out :=
  Proofs.Languages.Starlark.compares_iff_applyBinary op lhs rhs out

/-- The expression denotation is sound and complete for the big-step rules, including errors. -/
theorem eval_iff_denoteExpr (expr : ResolvedExpr) (frame : Frame) (result : Result Value) :
    Eval frame expr result ↔ denoteExpr expr frame = result :=
  ⟨Proofs.Languages.Starlark.denoteExpr_eq_of_eval,
    fun h => h ▸ Proofs.Languages.Starlark.eval_denoteExpr expr frame⟩

/-- The suite denotation is sound and complete for the big-step rules, including returns and errors. -/
theorem exec_iff_denoteStmt (stmt : ResolvedStmt) (frame : Frame) (result : Result Completion) :
    Exec frame stmt result ↔ denoteStmt stmt frame = result :=
  ⟨Proofs.Languages.Starlark.denoteStmt_eq_of_exec,
    fun h => h ▸ Proofs.Languages.Starlark.exec_denoteStmt stmt frame⟩

end Silmaril.Languages.Starlark
