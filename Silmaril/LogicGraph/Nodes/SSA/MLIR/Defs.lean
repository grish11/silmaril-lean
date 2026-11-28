module

public import Silmaril.Logic.Institution.Morphism
public import Silmaril.LogicGraph.Nodes.SSA.MLIR.CF.Defs
public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Project.Registry.IR.Defs
public import Silmaril.SSA.MLIR.Arith.Defs
public import Silmaril.SSA.MLIR.Institution.Thms
public import Silmaril.SSA.MLIR.LLVM.Defs

/-! Project records for the landed MLIR scalar subsets and pure institutions. -/

@[expose] public section

namespace Silmaril.LogicGraph.MLIR

open Silmaril.Logic.Institution

/-- The existing pure regionless MLIR institution, bundled for the logic graph. -/
def regionless : Inst :=
  ⟨Silmaril.MLIR.Institution.Signature false, Silmaril.MLIR.Institution.institution⟩

/-- The existing pure MLIR institution with isolated regions, bundled for the logic graph. -/
def isolated : Inst :=
  ⟨Silmaril.MLIR.Institution.Signature true, Silmaril.MLIR.Institution.institution⟩

end Silmaril.LogicGraph.MLIR

silmaril institution ssa.mlir.regionless := Silmaril.LogicGraph.MLIR.regionless
  (title := "Pure regionless MLIR")
silmaril institution ssa.mlir.isolated := Silmaril.LogicGraph.MLIR.isolated
  (title := "Pure MLIR with isolated regions")

silmaril ir_syntax_kind simple_ssa := "Simple SSA"
silmaril ir_syntax_kind isolated_simple_regions := "Isolated single-block regions"

silmaril ir_family mlir.llvm := "MLIR LLVM dialect"
silmaril ir_subset mlir.llvm.scalar := Silmaril.MLIR.LLVM.Block
  (family := mlir.llvm) (syntax_kind := simple_ssa) (title := "Scalar integer blocks")
  (doc := "One block over concrete signless integers, with a scalar return.")
silmaril ir_model mlir.llvm.scalar_eval := Silmaril.MLIR.LLVM.Block.eval
  (subset := mlir.llvm.scalar) (semantics := operational) (title := "Sequential evaluator")
  (doc := "Evaluates an admitted block in program order, returning bits or immediate UB for division by zero.")

silmaril ir_family mlir.arith := "MLIR Arith dialect"
silmaril ir_subset mlir.arith.isolated := Silmaril.MLIR.Arith.Block
  (family := mlir.arith) (syntax_kind := isolated_simple_regions)
  (title := "Scalar arithmetic with scoped application")
  (doc := "Modular integer operations and isolated single-block bodies with one explicit argument.")
silmaril ir_model mlir.arith.bitvector := Silmaril.MLIR.Arith.Block.denote
  (subset := mlir.arith.isolated) (semantics := denotational) (title := "Total bitvector denotation")
  (institution := ssa.mlir.isolated)
  (doc := "Arith.translate_denote proves agreement with the isolated institution's expression denotation at the arithmetic signature and bitvector model.")
