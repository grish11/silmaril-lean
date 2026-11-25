module

public import Silmaril.SSA.MLIR.Arith.LetIter.Defs
public import Silmaril.SSA.MLIR.Module.Defs

/-! # Typed MLIR

Use `Silmaril.MLIR.FuncModule` for an ordered collection of typed functions.
Use `Silmaril.MLIR.Arith.Block` for straight-line blocks and blocks with
isolated regions. Both lowerings share the same typed inputs and arithmetic
instructions. Import `Silmaril.SSA.MLIR.Thms` for correctness and observations.
-/

@[expose] public section

namespace Silmaril.MLIR.Arith

open Silmaril.Isotope.Institution.Observational (Model)

/-- The concrete observation model at a typed input. Primitive execution uses
modular arithmetic and has neither a fault nor a divergence outcome. -/
def Env.observationModel {Γ : List Width} (env : Env Γ) : Model.{0, 0, 0} Prim Γ.length where
  α := Atom
  σ := Unit
  instr := instr
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound := env.toLetIter

end Silmaril.MLIR.Arith
