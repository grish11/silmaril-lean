module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.InstructionMap

/-! # Relabelling the executable named lexical elaboration -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL

universe u w
variable {V K : Type w} {F G : Type u} {n : Nat} [DecidableEq V] [DecidableEq K]

theorem elaborateAt_eq (g : CFG V K F) (exits : List K) (captures : Fin n → V) :
    elaborateAt g exits captures g.blocks.length rfl = elaborate g exits captures :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.elaborateAt_eq g exits captures

/-- The elaborator preserves acceptance and failure under primitive
relabelling. The common count identifies the original positional indices. -/
theorem elaborateAt_mapOp (f : F → G) (g : CFG V K F) (exits : List K)
    (captures : Fin n → V) (count : Nat) (len : g.blocks.length = count)
    (mappedLen : (g.mapOp f).blocks.length = count) :
    elaborateAt (g.mapOp f) exits captures count mappedLen =
      (elaborateAt g exits captures count len).map (LambdaSSA.FiniteCFG.mapInstr f) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.elaborateAt_mapOp f g exits captures count len mappedLen

end Silmaril.Isotope.Bridge.NamedFlat
