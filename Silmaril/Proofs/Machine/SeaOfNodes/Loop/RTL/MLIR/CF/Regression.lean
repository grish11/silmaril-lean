module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF

open Silmaril.Machine.Lir (Word)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF

private abbrev word : Diamond.Ty Width := .value (.data i64)
private abbrev predicate : Diamond.Ty Width := .value .predicate

-- Update x by subtracting a captured stride. Continue when the updated x is
-- signed-less-than the limit, passing both the updated and the old x.
private def graph : Bank.Program [i64, i64, i64] [i64, i64] i64 [] [[word], [predicate]] where
  preheader := .nil
  header :=
    .cons (.arithmetic (.binary .subi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
      (.cons (.slt i64)
        (.cons (.output (0 : Fin 1) .head) (.cons (.arg (.tail (.tail .head))) .nil)) .nil)
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
    | .backedge => .cons (.output (0 : Fin 2) .head) (.cons (.arg (.tail (.tail (.tail .head)))) .nil)
  predicate := .output (1 : Fin 2) .head
  result := .output (0 : Fin 2) .head

private def target : Cfg TargetOp (Bank.Label [i64, i64] i64) [i64, i64, i64] [i64] :=
  Bank.lower graph

-- Check actual typed code, including operand order and both edge packets.
example : target.block .header =
    .letOp subi (.cons .here (.cons (.there (.there (.there .here))) .nil))
      (.letOp cmpiSlt (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil))
        (.terminator (.condBr .here
          ⟨.header, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩
          ⟨.exit, .cons (.there .here) .nil⟩))) :=
  rfl

private def captures (seed stride limit : Word) : Env [i64, i64, i64] :=
  .cons seed (.cons stride (.cons limit .nil))

private abbrev minWord : Word := BitVec.intMin 64
private abbrev maxWord : Word := BitVec.intMax 64

-- The wrapped value is negative. Unsigned or reversed comparison exits here.
example : (target.block .header).eval evalOp (fun term env => term.eval env)
    (.cons 0 (.cons 19 (captures 0 1 0))) =
    .inl ⟨.header, .cons (-1) (.cons 0 .nil)⟩ :=
  rfl

-- Subtracting 1 from the signed minimum wraps to the signed maximum.
example : target.run evalOp 3 (captures minWord 1 0) = some (.cons maxWord .nil) :=
  rfl

-- The first activation wraps to the signed minimum; the second exits with zero.
example : target.run evalOp 4 (captures 0 minWord 0) = some (.cons 0 .nil) :=
  rfl

example : graph.Returns model (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs (captures 0 minWord 0)) (0 : Word) :=
  (Bank.lower_returns_iff graph (captures 0 minWord 0) 0).mpr ⟨4, rfl⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF
