module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Terminator)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input Γ : List Width} {saved carried result : Width} {extra : List Width}

theorem Prefix.wrap_eval (leading : Prefix Input Γ)
    (tail : Block TargetOp (Label saved carried result extra) Γ [result]) (input : Env Input) :
    (leading.wrap tail).eval evalOp (fun term env => Terminator.eval env term) input =
      tail.eval evalOp (fun term env => Terminator.eval env term) (leading.eval input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.wrap_eval leading tail input

theorem Prefix.wrap_targets (leading : Prefix Input Γ)
    (tail : Block TargetOp (Label saved carried result extra) Γ [result]) :
    (shape.ofBlock (leading.wrap tail)).target = (shape.ofBlock tail).target :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.wrap_targets leading tail

theorem splitPrefix?_wrap {widths : List Width}
    {code : Block TargetOp (Label saved carried result extra) Input [result]}
    {leading : Prefix Input (widths ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) (widths ++ Input) [result]}
    (split : splitPrefix? code widths = some (leading, tail)) :
    leading.wrap tail = code :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.splitPrefix?_wrap split

theorem splitPrefix?_snoc {widths args : List Width} {w : Width} {newExtra : List Width}
    {code : Block TargetOp (Label saved carried result extra) Input [result]}
    {leading : Prefix Input (widths ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) (widths ++ Input) [result]}
    (split : splitPrefix? code widths = some (leading, tail))
    (op : TargetOp args w) (operands : Operands (widths ++ Input) args)
    (suffix : Block TargetOp (Label saved carried result newExtra) (w :: (widths ++ Input)) [result]) :
    splitPrefix? (leading.wrap (.letOp op operands suffix)) (w :: widths) =
      some (.snoc leading op operands, suffix) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved.splitPrefix?_snoc split op operands suffix

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved
