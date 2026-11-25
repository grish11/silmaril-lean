module

public import Silmaril.SSA.MLIR.SCF.ExtensionPrimitiveDefs

public section

namespace Silmaril.MLIR.SCF.PrimitiveExtension.Proofs

open CategoryTheory
open Silmaril.MLIR.Institution (OpArity Profile)

variable {Ty : Type} {S T U : FixedSignature Ty}

private theorem hom_ext {f g : S ⟶ T}
    (h : ∀ (arity : OpArity true) (profile : Profile arity Ty) (op : S.Op profile),
      f.symbol op = g.symbol op) : f = g := by
  cases f
  cases g
  congr
  funext arity profile op
  exact h arity profile op

variable (P : Primitives Ty)

theorem desc_unique (f : extend P S ⟶ U) :
    desc P (includeBase P S ≫ f) (includeFresh P S ≫ f) = f := by
  apply hom_ext
  intro _ _ op
  cases op <;> rfl

theorem extendMap_id (S : FixedSignature Ty) :
    extendMap P (𝟙 S) = 𝟙 (extend P S) := by
  apply hom_ext
  intro _ _ op
  cases op <;> rfl

theorem extendMap_comp (f : S ⟶ T) (g : T ⟶ U) :
    extendMap P (f ≫ g) = extendMap P f ≫ extendMap P g := by
  apply hom_ext
  intro _ _ op
  cases op <;> rfl

theorem multiply_naturality (f : S ⟶ T) :
    extendMap P (extendMap P f) ≫ multiply P T = multiply P S ≫ extendMap P f := by
  apply hom_ext
  intro _ _ op
  rcases op with (op | op) | op <;> rfl

theorem multiply_assoc (S : FixedSignature Ty) :
    extendMap P (multiply P S) ≫ multiply P S =
      multiply P (extend P S) ≫ multiply P S := by
  apply hom_ext
  intro _ _ op
  rcases op with ((op | op) | op) | op <;> rfl

theorem multiply_right_unit (S : FixedSignature Ty) :
    extendMap P (includeBase P S) ≫ multiply P S = 𝟙 (extend P S) := by
  apply hom_ext
  intro _ _ op
  cases op <;> rfl

theorem nullary_result_nonempty {arity : OpArity true} {profile : Profile arity Ty}
    (fresh : P.signature.Op profile) (hOperands : arity.operands = 0) (i : Fin arity.results)
    (M : Institution.Model (extend P S).toInstitution) :
    Nonempty (M.carrier (profile.result i)) := by
  have hRegions := P.regionless fresh
  exact ⟨M.op ((includeFresh P S).symbol fresh)
    (fun operand => Fin.elim0 (Fin.cast hOperands operand))
    (fun region => Fin.elim0 (Fin.cast hRegions region)) i⟩

end Silmaril.MLIR.SCF.PrimitiveExtension.Proofs
