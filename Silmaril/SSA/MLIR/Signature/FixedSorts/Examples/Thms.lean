module

public import Silmaril.SSA.MLIR.Signature.FixedSorts.Examples.Defs
public import Silmaril.SSA.MLIR.Institution.Thms

public section

namespace Silmaril.MLIR.Institution.Signature.FixedSorts.Examples

open CategoryTheory CategoryTheory.Limits
open Silmaril.MLIR.Arith (Width)

/-- The concrete renaming is the mediator supplied by the fixed-sort coproduct. -/
theorem colimitDesc_eq_mediator :
    (sum.isColimit core fresh).desc (BinaryCofan.mk (𝟙 core) freshToArith) = mediator :=
  sum.desc_unique _ _ _ ((sum.isColimit core fresh).fac _ ⟨WalkingPair.left⟩)
    ((sum.isColimit core fresh).fac _ ⟨WalkingPair.right⟩)

/-- Only the explicitly passed operand contributes to the yielded result. -/
theorem scopedDouble_denote (w : Width) (env : Assignment model.carrier (inputs w)) :
    (scopedDouble w).denote model env = BitVec.add (env 1 : BitVec w.val) (env 1) :=
  rfl

/-- Renaming the mixed term into Arith preserves its concrete denotation. -/
theorem scopedDouble_map_denote (w : Width) (env : Assignment Arith.model.carrier (inputs w)) :
    ((scopedDouble w).map toArith).denote Arith.model env =
      BitVec.add (env 1 : BitVec w.val) (env 1) :=
  ((scopedDouble w).denote_map toArith Arith.model env).trans (scopedDouble_denote w env)

example :
    (scopedDouble ⟨8, by decide⟩).denote model
      (Fin.cases (1 : BitVec 1) (fun _ => (200 : BitVec 8))) = (144 : BitVec 8) :=
  rfl

end Silmaril.MLIR.Institution.Signature.FixedSorts.Examples
