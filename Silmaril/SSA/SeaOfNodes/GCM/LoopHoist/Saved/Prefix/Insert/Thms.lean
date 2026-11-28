module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input Γ args : List Width} {w : Width}
variable {leading : Prefix Input Γ} {op : TargetOp args w} {operands : Operands Γ args}
variable {trailing : Nat} {edit : Insertion Input Γ w}

theorem insert?_length (done : leading.insert? op trailing operands = some edit) :
    edit.physical.length = Γ.length + 1 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.insert?_length done

/-- Physical references record the exact crossing distance of the new let
    and the shift of each retained definition or input. -/
theorem insert?_indices (done : leading.insert? op trailing operands = some edit) :
    edit.inserted.index = trailing ∧
    ∀ {width} (ref : Var Γ width),
      (edit.previous ref).index = if ref.index < trailing then ref.index else ref.index + 1 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.insert?_indices done

/-- Reading the spliced prefix via the typed correspondence gives precisely
    the append-order logical environment, including unchanged input slots. -/
theorem insert?_eval (done : leading.insert? op trailing operands = some edit) (input : Env Input) :
    ∀ {width} (ref : Var (w :: Γ) width),
      (edit.leading.eval input).get (edit.toPhysical ref) =
        (Env.cons (evalOp op (operands.eval (leading.eval input))) (leading.eval input)).get ref :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.insert?_eval done input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix
