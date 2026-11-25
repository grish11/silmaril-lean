module

public import Silmaril.SSA.MLIR.Signature.FixedSorts.Defs

public section

namespace Silmaril.Proofs.MLIR.Signature.FixedSorts

open CategoryTheory Silmaril.MLIR.Institution.Signature.FixedSorts

variable {withRegions : Bool} {Ty : Type}
variable {S T U : Silmaril.MLIR.Institution.Signature.FixedSorts withRegions Ty}

theorem desc_unique (f : S ⟶ U) (g : T ⟶ U) (h : sum S T ⟶ U)
    (hl : sum.inl S T ≫ h = f) (hr : sum.inr S T ≫ h = g) : h = sum.desc f g := by
  apply Hom.ext
  funext a p o
  cases o with
  | inl o => exact congrArg (fun k : S ⟶ U => k.symbol o) hl
  | inr o => exact congrArg (fun k : T ⟶ U => k.symbol o) hr

end Silmaril.Proofs.MLIR.Signature.FixedSorts
