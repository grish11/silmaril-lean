module

public import Silmaril.LogicGraph.Nodes.SSA.MLIR.Defs
public import Silmaril.SSA.MLIR.Institution.Arith.Thms

/-! Regression checks for the typed IR record handlers. -/

/-- error: silmaril ir_family: `doc` must be a string -/
#guard_msgs in
silmaril ir_family test.invalid := "Invalid documentation" (doc := 12)

/-- error: silmaril ir_subset: Nat.zero must declare a type or a family of types -/
#guard_msgs in
silmaril ir_subset test.invalid := Nat.zero
  (family := mlir.llvm) (syntax_kind := simple_ssa) (title := "Not a type")

/-- error: silmaril ir_model: Silmaril.MLIR.Arith.Block.denote must take a program of type Silmaril.MLIR.LLVM.Block -/
#guard_msgs in
silmaril ir_model test.mismatched := Silmaril.MLIR.Arith.Block.denote
  (subset := mlir.llvm.scalar) (semantics := denotational) (title := "Mismatched program type")

/-- error: silmaril ir_model: no `silmaril institution mlir.llvm` is declared or imported -/
#guard_msgs in
silmaril ir_model test.wrong_target := Silmaril.MLIR.LLVM.Block.eval
  (subset := mlir.llvm.scalar) (semantics := operational) (title := "Wrong target kind")
  (institution := mlir.llvm)

/-- error: silmaril ir_model "mlir.llvm.scalar_eval" is already declared in Silmaril.LogicGraph.Nodes.SSA.MLIR.Defs -/
#guard_msgs in
silmaril ir_model mlir.llvm.scalar_eval := Silmaril.MLIR.LLVM.Block.eval
  (subset := mlir.llvm.scalar) (semantics := operational) (title := "Duplicate model")

open Silmaril.MLIR in
example {Γ : List Arith.Width} {w : Arith.Width} (block : Arith.Block Γ w) (env : Arith.Env Γ) :
    (Institution.Arith.translate block).denote Institution.Arith.model
      (Institution.Arith.assignment env) = block.denote env :=
  Institution.Arith.translate_denote block env

/-- error: silmaril ir_model: Silmaril.MLIR.CF.SwitchAssert.Cfg.run must take a program of type Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.TargetProgram -/
#guard_msgs in
silmaril ir_model test.mismatched_cf := Silmaril.MLIR.CF.SwitchAssert.Cfg.run
  (subset := mlir.cf.basic_scalar_loop) (semantics := operational) (title := "Mismatched CFG")

open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution in
example {B : Profile} (g : TargetProgram B) :
    (TargetSentence.terminates g).Holds ↔ ∀ input, (observe g input).Dom :=
  Iff.rfl

open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution in
example {B : Profile} (S : Signature) (s : SourceSentence B S.left) :
    (translate S s).Holds ↔ s.val.Holds (sourceModel S) :=
  satisfaction_induced S s
