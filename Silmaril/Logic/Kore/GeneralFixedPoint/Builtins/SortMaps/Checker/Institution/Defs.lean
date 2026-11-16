module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Paths.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
open CategoryTheory Silmaril.Logic.Institution

/-- Fixed-alias source receipts and all actual native homomorphisms between
models satisfying the package's literal and hook laws. -/
def sourceRoom (A : ValidatedPackage) : Room :=
  ⟨SourceSentence A.package,
    Cat.of (@Model A.package.base.bindings A.package.base.scope A.package.base.literalPrefix
      A.package.base.literals A.package.base.hooks), SourceSentence.Satisfies⟩

/-- The source sentence action is computed from recursive checker transport;
the model action is the existing restricted builtin-model reduct. -/
def sourceCorridor {A B : ValidatedPackage} (path : A ⟶ B) : sourceRoom A ⟶ sourceRoom B :=
  ⟨fun p => p.mapPath path A.profiles, Hom.reductFunctor path.semantic,
    fun M p => p.mapPath_satisfies path A.profiles M⟩

def sourceInstitution : ValidatedPackage ⥤ Room where
  obj := sourceRoom
  map := sourceCorridor
  map_id A := by
    apply Room.hom_ext
    · rfl
    · exact Hom.reductFunctor_id A.package.base
  map_comp path next := by
    apply Room.hom_ext
    · funext p
      exact p.mapPath_append path next _
    · change Hom.reductFunctor (Path.semantic (Path.append path next)) = _
      rw [Path.semantic_append]
      exact Hom.reductFunctor_comp path.semantic next.semantic

/-- `sourceInstitution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def sourceInst := (⟨ValidatedPackage, sourceInstitution⟩ : Silmaril.Logic.Institution.Inst)

/-- Lower an actual source receipt while retaining its actual model. -/
def sourceLoweringCorridor (A : ValidatedPackage) :
    sourceRoom A ⟶ SortMaps.nativeRoom A.package.base :=
  ⟨SourceSentence.lower, 𝟭 _, fun M p => (p.satisfies_lower M).symm⟩

/-- Naturality is the exact lower/native equation for every source path. -/
def sourceLowering : sourceInstitution ⟶
    (validatedToSurface ⋙ toSemantic) ⋙ SortMaps.nativeInstitution where
  app := sourceLoweringCorridor
  naturality := by
    intro A B path
    apply Room.hom_ext
    · funext p
      exact p.mapPath_lower path A.profiles
    · rfl

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
