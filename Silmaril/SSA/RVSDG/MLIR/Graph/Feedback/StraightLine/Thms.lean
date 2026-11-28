module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.StraightLine.Defs
import Silmaril.Proofs.SSA.RVSDG.MLIR.Graph.Feedback.StraightLine.Correctness

/-! Observation of a typed continuation at the end of a straight-line block. -/

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback

open OrderedRuntime.Structured (Values)

universe u v w z
variable {V : Type u} {Op Target : Dialect.{u,v} V PUnit.{u+1}}
variable {M : Type (max u w) → Type z} [Monad M] [LawfulMonad M] {value : V → Type w}
variable {entry outs result : Ports (PortSort V)} {past : List (Ports (PortSort V))}

/-- The continuation sees the yielded values and the original entry group.
In particular, it executes after all the body's effects. -/
theorem Code.runStraightLine_mapYield
    (opcode : ∀ {ins outs}, Op ins outs → Target ins outs)
    (finish : ∀ {past}, Operands (entry :: past) outs → StraightBlock Target (entry :: past) result)
    (step : ∀ {ins outs}, Op ins outs → Tuple (Values value) ins → M (Tuple (Values value) outs))
    (targetStep : ∀ {ins outs}, Target ins outs → Tuple (Values value) ins → M (Tuple (Values value) outs))
    (after : Tuple (Values value) outs → Tuple (Values value) entry → M (Tuple (Values value) result))
    (op_eq : ∀ {ins outs} (op : Op ins outs) (input : Tuple (Values value) ins),
      targetStep (opcode op) input = step op input)
    (finish_eq : ∀ {past} (wires : Operands (entry :: past) outs)
        (env : Locals (Values value) (entry :: past)),
      (finish wires).val.runStraightLine targetStep (finish wires).property env = after (wires.read .nil env) env.1)
    (code : Code Op (entry :: past) outs) (admitted : code.StraightLine)
    (env : Locals (Values value) (entry :: past)) :
    let lowered := code.mapYield opcode finish admitted
    lowered.val.runStraightLine targetStep lowered.property env =
      (code.runStraightLine step admitted env >>= fun values => after values env.1) :=
  Proofs.runStraightLine_mapYield opcode finish step targetStep after op_eq finish_eq code admitted env

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback
