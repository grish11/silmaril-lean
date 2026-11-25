module

public import Silmaril.SSA.MLIR.SCF.ExtensionPrimitiveDefs
public import Mathlib.CategoryTheory.Monad.Basic
import Silmaril.Proofs.SSA.MLIR.SCF.ExtensionPrimitiveLaws

@[expose] public section

namespace Silmaril.MLIR.SCF.PrimitiveExtension

open CategoryTheory
open Silmaril.MLIR.Institution (OpArity Profile)

variable {Ty : Type} {S T U : FixedSignature Ty} (P : Primitives Ty)

theorem includeBase_injective {arity : OpArity true} {profile : Profile arity Ty} :
    Function.Injective ((includeBase P S).symbol (profile := profile)) := by
  intro _ _ h
  exact Sum.inl.inj h

theorem includeFresh_injective {arity : OpArity true} {profile : Profile arity Ty} :
    Function.Injective ((includeFresh P S).symbol (profile := profile)) := by
  intro _ _ h
  exact Sum.inr.inj h

/-- The old and fresh injections remain disjoint even at the same full profile. -/
theorem old_ne_fresh {arity : OpArity true} {profile : Profile arity Ty}
    (old : S.Op profile) (fresh : P.signature.Op profile) :
    (includeBase P S).symbol old ≠ (includeFresh P S).symbol fresh :=
  Sum.inl_ne_inr

@[simp] theorem includeBase_desc (base : S ⟶ U) (fresh : P.signature ⟶ U) :
    includeBase P S ≫ desc P base fresh = base := rfl

@[simp] theorem includeFresh_desc (base : S ⟶ U) (fresh : P.signature ⟶ U) :
    includeFresh P S ≫ desc P base fresh = fresh := rfl

theorem desc_unique (f : extend P S ⟶ U) :
    desc P (includeBase P S ≫ f) (includeFresh P S ≫ f) = f :=
  Proofs.desc_unique P f

/-- The coproduct universal property in the fixed-sort, full-profile category. -/
def extendHomEquiv (S U : FixedSignature Ty) :
    (extend P S ⟶ U) ≃ ((S ⟶ U) × (P.signature ⟶ U)) where
  toFun f := (includeBase P S ≫ f, includeFresh P S ≫ f)
  invFun maps := desc P maps.1 maps.2
  left_inv := desc_unique P
  right_inv _ := rfl

theorem extendMap_id (S : FixedSignature Ty) :
    extendMap P (𝟙 S) = 𝟙 (extend P S) :=
  Proofs.extendMap_id P S

theorem extendMap_comp (f : S ⟶ T) (g : T ⟶ U) :
    extendMap P (f ≫ g) = extendMap P f ≫ extendMap P g :=
  Proofs.extendMap_comp P f g

/-- The endofunctor adds the same fresh primitive symbols to each signature. -/
def extendFunctor : FixedSignature Ty ⥤ FixedSignature Ty where
  obj := extend P
  map := extendMap P
  map_id := extendMap_id P
  map_comp := extendMap_comp P

theorem multiply_naturality (f : S ⟶ T) :
    extendMap P (extendMap P f) ≫ multiply P T = multiply P S ≫ extendMap P f :=
  Proofs.multiply_naturality P f

theorem multiply_assoc (S : FixedSignature Ty) :
    extendMap P (multiply P S) ≫ multiply P S = multiply P (extend P S) ≫ multiply P S :=
  Proofs.multiply_assoc P S

theorem multiply_right_unit (S : FixedSignature Ty) :
    extendMap P (includeBase P S) ≫ multiply P S = 𝟙 (extend P S) :=
  Proofs.multiply_right_unit P S

/-- The fixed-sort extension monad. The unit is the base injection and the
multiplication identifies corresponding symbols in the two fresh copies. -/
def extensionMonad : CategoryTheory.Monad (FixedSignature Ty) where
  toFunctor := extendFunctor P
  η := { app := includeBase P, naturality := fun _ _ _ => rfl }
  μ := { app := multiply P, naturality := fun _ _ f => multiply_naturality P f }
  assoc := multiply_assoc P
  left_unit _ := rfl
  right_unit := multiply_right_unit P

/-- A nullary fresh symbol forces each of its result carriers to be inhabited in
every total model of the extension, including after restriction to the base. -/
theorem nullary_result_nonempty {arity : OpArity true} {profile : Profile arity Ty}
    (fresh : P.signature.Op profile) (hOperands : arity.operands = 0) (i : Fin arity.results)
    (M : Institution.Model (extend P S).toInstitution) :
    Nonempty (M.carrier (profile.result i)) :=
  Proofs.nullary_result_nonempty P fresh hOperands i M

end Silmaril.MLIR.SCF.PrimitiveExtension
