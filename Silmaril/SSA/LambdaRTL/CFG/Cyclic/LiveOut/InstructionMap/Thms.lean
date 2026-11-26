module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.InstructionMap.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOutInstructionMap

/-! # Primitive relabelling of explicit live-out reads -/

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut

universe u v

/-- The written exit transformation commutes with relabelling. The selected
registers and first-match lookup are independent of the primitive alphabet. -/
theorem attach_mapOp {V K : Type u} {F G : Type v} [DecidableEq K]
    (f : F → G) (fields : K → List V) (g : CFG V K F) :
    attach fields (g.mapOp f) = (attach fields g).mapOp f :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut.attach_mapOp f fields g

/-- The primitive reduct retains the structural operations used to read the
ordered exit tuple. -/
theorem project_reduct {V K : Type u} {F G : Type v} {M : Type u → Type u} {α : Type u}
    (f : F → G) (model : Model G M α) (fields : K → List V) (out : Transfer V K α) :
    project (model.reduct f) fields out = project model fields out :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut.project_reduct f fields model out

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut
