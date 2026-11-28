module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF.Defs
public import Silmaril.Machine.RTL.Thms

/-! Exact word and predicate encoding across MLIR CF and machine RTL. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF

open Silmaril.Machine.Lir (Binop Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Op)

open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)

/-- Flag-free subtraction and RTL subtraction have the same result at every bit pattern. -/
theorem subi_eq_rtl (lhs rhs : Word) :
    Binop.sub.eval lhs rhs = some (evalOp subi (.cons lhs (.cons rhs .nil))) :=
  rfl

/-- MLIR's comparison bit zero-extends to the exact RTL predicate word. -/
theorem cmpiSlt_eq_rtl (lhs rhs : Word) :
    (Binop.cmp .lts).eval lhs rhs =
      some ((evalOp cmpiSlt (.cons lhs (.cons rhs .nil))).setWidth 64) := by
  change some (ofBool (lhs.slt rhs)) = some ((BitVec.ofBool (lhs.slt rhs)).setWidth 64)
  cases lhs.slt rhs <;> rfl

/-- RTL executes the same subtraction and preserves the full memory. -/
theorem exec_subi {R : Type} [DecidableEq R] (dst lhs rhs : R) (frame : Frame R) (mem : Memory)
    (left right : Word) (readLeft : frame.get lhs = some left) (readRight : frame.get rhs = some right) :
    (Op.binary .sub dst lhs rhs).exec frame mem =
      some (frame.set dst (evalOp subi (.cons left (.cons right .nil))), mem) := by
  simp only [Op.exec, readLeft, readRight, Option.bind_some, subi_eq_rtl, Option.map_some]

/-- RTL compares the same ordered operands and preserves the full memory. -/
theorem exec_cmpiSlt {R : Type} [DecidableEq R] (dst lhs rhs : R) (frame : Frame R) (mem : Memory)
    (left right : Word) (readLeft : frame.get lhs = some left) (readRight : frame.get rhs = some right) :
    (Op.binary (.cmp .lts) dst lhs rhs).exec frame mem =
      some (frame.set dst ((evalOp cmpiSlt (.cons left (.cons right .nil))).setWidth 64), mem) := by
  simp only [Op.exec, readLeft, readRight, Option.bind_some, cmpiSlt_eq_rtl, Option.map_some]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF
