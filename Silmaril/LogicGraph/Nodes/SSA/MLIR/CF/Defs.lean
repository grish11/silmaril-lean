module

public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Project.Registry.IR.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Thms

/-! Project records for typed MLIR CF fragments. -/

silmaril ir_syntax_kind typed_ssa_cfg := "Typed SSA control-flow graphs"
silmaril ir_family mlir.cf := "MLIR CF dialect"

silmaril institution ssa.mlir.cf.scalar_loop :=
  Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.targetInst
  (title := "MLIR CF at a fixed scalar loop profile")

silmaril ir_subset mlir.cf.basic_scalar_loop :=
  Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.TargetProgram
  (family := mlir.cf) (syntax_kind := typed_ssa_cfg) (title := "Basic CF at a scalar loop profile")
  (doc := "Typed Basic CF with fixed captured input widths, one scalar latch, and one result width.")
silmaril ir_model mlir.cf.basic_scalar_loop_part :=
  Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.observe
  (subset := mlir.cf.basic_scalar_loop) (semantics := denotational)
  (title := "Partial return observation at the scalar profile")
  (institution := ssa.mlir.cf.scalar_loop)
  (doc := "TargetSentence.Holds uses this observation. satisfaction_induced preserves and reflects satisfaction of admitted equations and termination sentences.")

silmaril ir_subset mlir.cf.switch_assert := Silmaril.MLIR.CF.SwitchAssert.Cfg
  (family := mlir.cf) (syntax_kind := typed_ssa_cfg) (title := "CF switch and assertion graphs")
  (doc := "Typed CFGs with switch cases and assertions that can abort execution.")
silmaril ir_model mlir.cf.switch_assert_run := Silmaril.MLIR.CF.SwitchAssert.Cfg.run
  (subset := mlir.cf.switch_assert) (semantics := operational) (title := "Fuelled block execution")
  (doc := "Uses one unit of fuel per block. A budget may exhaust before a return or an abort.")
silmaril ir_model mlir.cf.switch_assert_part := Silmaril.MLIR.CF.SwitchAssert.Cfg.denotePart
  (subset := mlir.cf.switch_assert) (semantics := denotational) (title := "Partial return or abort")
  (doc := "Cfg.mem_denotePart_iff characterizes defined outcomes by finite execution, and divergence is undefined.")
