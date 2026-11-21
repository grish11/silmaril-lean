module

public import Silmaril.Wasm.Sublanguages.Defs
public import Mathlib.CategoryTheory.Types.Basic
import Silmaril.Proofs.Wasm.Sublanguages.Inclusions

public section

namespace Silmaril.Wasm.Sublanguages

open CategoryTheory

namespace Inclusion

variable {A B : Language}

theorem instr_injective (arrow : Inclusion A B) : Function.Injective arrow.instr :=
  fun {left right} eq => A.toInstr.injective
    ((arrow.instr_comm left).symm.trans ((congrArg B.toInstr eq).trans (arrow.instr_comm right)))

theorem func_injective (arrow : Inclusion A B) : Function.Injective arrow.func :=
  fun {left right} eq => A.toFunc.injective
    ((arrow.func_comm left).symm.trans ((congrArg B.toFunc eq).trans (arrow.func_comm right)))

/-- Commuting inclusions between chosen images are unique, though the
source and target languages need not be equal. -/
instance : Subsingleton (Inclusion A B) where
  allEq := Proofs.inclusion_unique

@[simp] theorem comp_intoCore (arrow : Inclusion A B) :
    arrow.comp B.intoCore = A.intoCore := Subsingleton.elim _ _

theorem admits (arrow : Inclusion A B) {caps : Models.FeatureSet} {mod : A.Module} :
    B.Admits caps (arrow.mod mod) ↔ A.Admits caps mod := by
  unfold Language.Admits
  rw [arrow.mod_comm]

end Inclusion

/-- The object of modules and the inclusion maps, without the feature guard. -/
def moduleFunctor : Language ⥤ Type where
  obj language := language.Module
  map arrow := ↾(Inclusion.mod arrow)
  map_id _ := rfl
  map_comp _ _ := rfl

instance : moduleFunctor.Faithful where
  map_injective := fun _ => Proofs.inclusion_unique _ _

theorem Language.admits_mono (language : Language) {small large : Models.FeatureSet}
    (le : small ≤ large) {mod : language.Module} (admit : language.Admits small mod) :
    language.Admits large mod := Models.module_mono le _ admit

/-- Both growing the syntax image and allowing more capabilities preserve admission. -/
theorem Language.admittedImage_mono {A B : Language} (arrow : Inclusion A B)
    {small large : Models.FeatureSet} (le : small ≤ large) :
    A.admittedImage small ⊆ B.admittedImage large := by
  rintro coreMod ⟨mod, admitted, eq⟩
  exact ⟨arrow.mod mod, arrow.admits.mpr (A.admits_mono le admitted), (arrow.mod_comm mod).trans eq⟩

/-- Send a capability assignment to the set of admitted exact Core images. -/
def Language.admission (language : Language) : Models.FeatureSet →o Set Wasm.Module where
  toFun := language.admittedImage
  monotone' := fun {_ _} le => language.admittedImage_mono (Inclusion.identity language) le

/-- Every natively checked V2 module belongs to the translation domain. -/
def wasm2OfChecked {ports : Profiles.HasTyping.Interface Profiles.Wasm2}
    (source : Profiles.CheckedModule Profiles.Wasm2 ports) : wasm2.Module :=
  ⟨source.val, Profiles.Injections.wasm2Module_isSome source⟩

/-- The underlying Core syntax is exactly the checked image at the translated interface. -/
theorem wasm2_checked_image {ports : Profiles.HasTyping.Interface Profiles.Wasm2}
    (source : Profiles.CheckedModule Profiles.Wasm2 ports) :
    wasm2.toModule (wasm2OfChecked source) = (Profiles.Injections.checkedWasm2ToWasm3 source).val :=
  Option.some.inj ((Profiles.Injections.wasm2ToWasm3.onDomain_spec (wasm2OfChecked source)).symm.trans
    (Profiles.Injections.checkedWasm2ToWasm3_erasure source))

end Silmaril.Wasm.Sublanguages
