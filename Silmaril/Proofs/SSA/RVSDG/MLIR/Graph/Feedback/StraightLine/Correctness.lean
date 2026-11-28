module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.StraightLine.Defs

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Proofs

open OrderedRuntime.Structured (Values)

universe u v w z
variable {V : Type u} {Op Target : Dialect.{u,v} V PUnit.{u+1}}
variable {M : Type (max u w) → Type z} [Monad M] [LawfulMonad M] {value : V → Type w}
variable {entry outs result : Ports (PortSort V)}

variable (opcode : ∀ {ins outs}, Op ins outs → Target ins outs)
variable (finish : ∀ {past}, Operands (entry :: past) outs → StraightBlock Target (entry :: past) result)
variable (step : ∀ {ins outs}, Op ins outs → Tuple (Values value) ins → M (Tuple (Values value) outs))
variable (targetStep : ∀ {ins outs}, Target ins outs → Tuple (Values value) ins → M (Tuple (Values value) outs))
variable (after : Tuple (Values value) outs → Tuple (Values value) entry → M (Tuple (Values value) result))
variable (op_eq : ∀ {ins outs} (op : Op ins outs) (input : Tuple (Values value) ins),
  targetStep (opcode op) input = step op input)
variable (finish_eq : ∀ {past} (wires : Operands (entry :: past) outs) (env : Locals (Values value) (entry :: past)),
  (finish wires).val.runStraightLine targetStep (finish wires).property env = after (wires.read .nil env) env.1)

include op_eq finish_eq in
theorem runStraightLine_mapYield :
    {past : List (Ports (PortSort V))} → (code : Code Op (entry :: past) outs) →
    (admitted : code.StraightLine) → (env : Locals (Values value) (entry :: past)) →
    let lowered := code.mapYield opcode finish admitted
    lowered.val.runStraightLine targetStep lowered.property env =
      (code.runStraightLine step admitted env >>= fun values => after values env.1)
  | _, .yield wires, _, env => by
    simpa only [Code.mapYield, Code.runStraightLine, pure_bind] using finish_eq wires env
  | _, .prim op args rest, admitted, env => by
    simp only [Code.mapYield, Code.runStraightLine, op_eq, bind_assoc]
    apply congrArg (fun runRest => step op (args.read .nil env) >>= runRest)
    funext values
    exact runStraightLine_mapYield rest admitted (env.snoc values)
  | _, .choose .., admitted, _ => False.elim admitted
  | _, .feedback .., admitted, _ => False.elim admitted

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Proofs
