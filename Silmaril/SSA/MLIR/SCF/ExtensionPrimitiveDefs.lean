module

public import Silmaril.SSA.MLIR.Institution.Defs

/-! Fixed-sort signatures for adjoining regionless primitives to an isolated-region profile. -/

@[expose] public section

namespace Silmaril.MLIR.SCF.PrimitiveExtension

open CategoryTheory
open Silmaril.MLIR.Institution (OpArity Profile)

/-- Symbols indexed by the full ordered MLIR institution profile over a common sort type. -/
structure FixedSignature (Ty : Type) where
  Op : {arity : OpArity true} → Profile arity Ty → Type

/-- Maps fix the sorts and the full profile, including the profiles of all region slots. -/
structure Hom {Ty : Type} (S T : FixedSignature Ty) where
  symbol : ∀ {arity : OpArity true} {profile : Profile arity Ty}, S.Op profile → T.Op profile

instance {Ty : Type} : Category (FixedSignature Ty) where
  Hom := Hom
  id _ := ⟨id⟩
  comp f g := ⟨fun op => g.symbol (f.symbol op)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {Ty : Type} {S T U : FixedSignature Ty}

/-- View a fixed-sort symbol family as an isolated-region institution signature. -/
def FixedSignature.toInstitution (S : FixedSignature Ty) : Institution.Signature true :=
  ⟨Ty, S.Op⟩

/-- View a profile-preserving map as an institution map with identity sort component. -/
def Hom.toInstitution (f : S ⟶ T) : S.toInstitution ⟶ T.toInstitution :=
  ⟨id, f.symbol⟩

/-- Realize fixed-sort signatures and their maps in the MLIR institution. -/
def toInstitution (Ty : Type) : FixedSignature Ty ⥤ Institution.Signature true where
  obj := FixedSignature.toInstitution
  map := Hom.toInstitution
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The fixed family of fresh primitives may only have symbols at zero-region profiles. -/
structure Primitives (Ty : Type) where
  signature : FixedSignature Ty
  regionless : ∀ {arity : OpArity true} {profile : Profile arity Ty},
    signature.Op profile → arity.regions.count = 0

/-- Adjoin a disjoint copy of the fixed primitive family at each profile. -/
def extend (P : Primitives Ty) (S : FixedSignature Ty) : FixedSignature Ty where
  Op profile := Sum (S.Op profile) (P.signature.Op profile)

/-- Include the original symbols in the extended signature. -/
def includeBase (P : Primitives Ty) (S : FixedSignature Ty) : S ⟶ extend P S :=
  ⟨Sum.inl⟩

/-- Include the fresh primitive symbols in the extended signature. -/
def includeFresh (P : Primitives Ty) (S : FixedSignature Ty) : P.signature ⟶ extend P S :=
  ⟨Sum.inr⟩

/-- Interpret the two copies independently by maps into a common signature. -/
def desc (P : Primitives Ty) (base : S ⟶ U) (fresh : P.signature ⟶ U) :
    extend P S ⟶ U :=
  ⟨Sum.elim base.symbol fresh.symbol⟩

/-- Extend a map by fixing all the newly adjoined symbols. -/
def extendMap (P : Primitives Ty) (f : S ⟶ T) : extend P S ⟶ extend P T :=
  desc P (f ≫ includeBase P T) (includeFresh P T)

/-- Fold the two fresh copies together, fixing the original symbols. -/
def multiply (P : Primitives Ty) (S : FixedSignature Ty) : extend P (extend P S) ⟶ extend P S :=
  desc P (𝟙 (extend P S)) (includeFresh P S)

end Silmaril.MLIR.SCF.PrimitiveExtension
