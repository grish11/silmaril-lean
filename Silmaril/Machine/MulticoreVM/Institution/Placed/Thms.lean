module

public import Silmaril.Machine.MulticoreVM.Institution.Placed.Defs
public import Silmaril.Machine.MulticoreVM.Institution.Projection.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Institution.Placed

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory

universe u

open Proofs.Machine.MulticoreVM.Institution
  (mapPlaced_id mapPlaced_comp mapCoreLocal_id mapCoreLocal_comp
    placedToNamed_natural placedToCore_natural)

/-- The full chronological observation profile of the placed VM. -/
def placedWords : Sig.{u} ⥤ Type u where
  obj := Sig.PlacedWord
  map f := TypeCat.ofHom (Sig.Hom.mapPlaced f)
  map_id _ := by exact TypeCat.homEquiv.injective (funext mapPlaced_id)
  map_comp f g := by exact TypeCat.homEquiv.injective (funext (mapPlaced_comp f g))

/-- Chronological core-local words, with no quotient on core IDs. -/
def coreLocalWords : Sig.{u} ⥤ Type u where
  obj := Sig.CoreLocalWord
  map f := TypeCat.ofHom (Sig.Hom.mapCoreLocal f)
  map_id _ := by exact TypeCat.homEquiv.injective (funext mapCoreLocal_id)
  map_comp f g := by exact TypeCat.homEquiv.injective (funext (mapCoreLocal_comp f g))

/-- The placed VM's chronological thread projection. -/
def placedToNamed : placedWords.{u} ⟶ namedWords.{u} where
  app _ := TypeCat.ofHom Placed.threadWord
  naturality {A B} f := by
    exact TypeCat.homEquiv.injective (funext (placedToNamed_natural f))

/-- The placed VM's chronological core projection. -/
def placedToCore : placedWords.{u} ⟶ coreLocalWords.{u} where
  app _ := TypeCat.ofHom Placed.coreWord
  naturality {A B} f := by
    exact TypeCat.homEquiv.injective (funext (placedToCore_natural f))

/-- The named projection of a placed behavior refines the abstract VM when its instructions
refine the abstract transition. This compares two operational models starting at related states. -/
theorem placed_named_subset {A : Sig.{u}} {Core Thread Choice : Type u} [DecidableEq A.CoreId]
    {instruction : Placed.Instruction A.CoreId A.ThreadId Core Thread Choice A.Event}
    {step : Transition (A.ThreadId → Option Thread) A.ThreadId Choice A.Event}
    (refines : instruction.Refines step)
    (initial : Placed.Config A.CoreId A.ThreadId Core Thread) :
    (placedToNamed.app A) '' ofPlaced (A := A) instruction initial ⊆
      namedModel (A := A) step initial.threads :=
  Proofs.Machine.MulticoreVM.Institution.placed_named_subset refines initial

end Silmaril.Machine.MulticoreVM.Institution
