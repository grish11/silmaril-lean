module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Institution.Defs
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.SurfaceControl

-- variant-of: SurfaceControl.source_square | style: generic-receipt | see-also: SurfaceControl.lower_native
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface.Examples
open CategoryTheory

/-- The populated source has literal zero, integer equality, Boolean negation
and a real alias. Only its source checker receipt is supplied. -/
def source : ValidatedPackage := ⟨SurfaceControl.sourcePackage, by decide +kernel⟩

def target : ValidatedPackage :=
  ⟨SurfaceControl.targetPackage, SurfaceControl.step.literalProfiles_forward source.profiles⟩

def path : source ⟶ target := .cons SurfaceControl.step (.nil _)

def input : SourceSentence source.package :=
  SourceSentence.ofChecked RawControls.sourceReceipt rfl

/-- The general action constructs the actual target checker receipt. -/
def output : SourceSentence target.package := input.mapPath path source.profiles

example : output.raw = RawControls.aliasRaw := by
  change raw PopulatedControls.renameSort id RawControls.aliasRaw = _
  simp [raw, RawControls.aliasRaw]
example : output.fuel = 12 := rfl
example : path.semantic.native.sorts "CfgA" = path.semantic.native.sorts "CfgB" := by decide +kernel

theorem output_lower : output.lower =
    Matching.SortMaps.Hom.generalSentence path.semantic.native input.lower :=
  input.mapPath_lower path source.profiles

theorem output_satisfies
    (M : @Model target.package.base.bindings target.package.base.scope
      target.package.base.literalPrefix target.package.base.literals target.package.base.hooks) :
    output.Satisfies M ↔ input.Satisfies (Hom.reduct path.semantic M) :=
  input.mapPath_satisfies path source.profiles M

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface.Examples
