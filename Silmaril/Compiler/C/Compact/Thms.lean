module

public import Silmaril.Compiler.C.Compact.Defs
import Silmaril.Proofs.Compiler.C.Compact

public section
namespace Silmaril.Compiler.C.Compact

open Silmaril.Compile.C.Sem Silmaril.Cerberus.Ail

/-- A successful expression projection preserves the result, including a C0 stop, and
does not change the related Ail environment. This is about C0 expression evaluation,
not a simulation of the full Cerberus Core transition system. -/
theorem ExprProjection.eval_eq {scope : List Silmaril.Cerberus.Sym} {ail : TypedExpression}
    (projection : ExprProjection scope ail) (program : C0.Prog) (fn : C0.FunDef) (env : C0.Env)
    (read : Nat → Except C0.Stop Int)
    (related : ∀ index symbol, scope[index]? = some symbol → read index = C0.readVar fn env symbol)
    (fuel : Nat) (enough : projection.expr.depth ≤ fuel) :
    C0.evalE program fuel fn ail env = (projection.expr.eval read).map (·, env) :=
  Proofs.Compiler.C.Compact.eval_eq projection.projects program fn env read related fuel enough

end Silmaril.Compiler.C.Compact
