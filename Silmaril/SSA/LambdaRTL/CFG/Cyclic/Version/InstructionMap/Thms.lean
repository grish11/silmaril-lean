module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.VersionInstructionMap

/-! # Primitive relabelling of the actual cyclic versioner output -/

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning

universe u w

/-- Version allocation and destination packet layouts depend on register reads
and labels. Primitive relabelling commutes with the literal generated table. -/
theorem compile_mapOp {V K : Type w} {F G : Type u}
    [DecidableEq V] [DecidableEq K] (f : F → G) (g : CFG V K F) :
    compile (g.mapOp f) = (compile g).mapOp f :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicVersion.compile_mapOp f g

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning
