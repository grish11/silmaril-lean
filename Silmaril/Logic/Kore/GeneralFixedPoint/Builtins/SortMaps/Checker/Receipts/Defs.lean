module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Elaboration.Thms
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.LoweringProfiles.Thms
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Institution

-- Builtin sort names are chosen separately by each package.
set_option linter.concreteInstances false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
open CategoryTheory Silmaril.Logic.Institution

/-- A source package whose literal bindings pass the finite profile check. -/
structure ValidatedPackage where
  package : Package
  profiles : literalProfiles package = true

/-- Actual checked source definitions always produce validated packages. -/
def validatedSource [bindings : SortBindings] (d : CheckedDefinition) : ValidatedPackage :=
  ⟨checkedSource d, checkedSource_literalProfiles d⟩

instance : Category ValidatedPackage where
  Hom A B := Path A.package B.package
  id A := .nil A.package
  comp := Path.append
  id_comp _ := rfl
  comp_id := Path.append_nil
  assoc := Path.append_assoc

def validatedToSurface : ValidatedPackage ⥤ Package where
  obj := ValidatedPackage.package
  map p := p
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A receipt for the package's fixed alias list. Each field is retained from
an actual successful run of the fuel-bounded source checker. -/
structure SourceSentence (A : Package) where
  moduleIndex : Nat
  fuel : Nat
  sets : Names
  objects : Names
  sort : String
  raw : RawPattern
  typed : @Pattern A.base.scope sets objects sort
  accepted : elaboratePackage A moduleIndex fuel sets objects sort raw = some typed
  admitted : typed.admissible = true

/-- Forget only the fixed-alias invariant, producing the existing receipt. -/
def SourceSentence.toChecked {A : Package} (p : SourceSentence A) :
    @CheckedSentence A.base.bindings A.base.scope A.base.literals A.base.literalPrefix := by
  letI : SortBindings := A.base.bindings
  exact {
    aliases := A.aliases
    moduleIndex := p.moduleIndex
    fuel := p.fuel
    sets := p.sets
    objects := p.objects
    sort := p.sort
    raw := p.raw
    typed := p.typed
    accepted := p.accepted
    admitted := p.admitted
  }

/-- Existing receipts enter the source API when their actual alias list is the
package alias list. No new checker equation is assumed. -/
def SourceSentence.ofChecked {A : Package}
    (p : @CheckedSentence A.base.bindings A.base.scope A.base.literals A.base.literalPrefix)
    (aliases : @CheckedSentence.aliases A.base.bindings _ _ _ p = A.aliases) : SourceSentence A := by
  letI : SortBindings := A.base.bindings
  exact {
    moduleIndex := p.moduleIndex
    fuel := p.fuel
    sets := p.sets
    objects := p.objects
    sort := p.sort
    raw := p.raw
    typed := p.typed
    accepted := by
      change @Checking.elaborate A.base.bindings A.base.scope A.aliases A.base.literals
        A.base.literalPrefix p.moduleIndex p.fuel p.sets p.objects p.sort p.raw = _
      rw [← aliases]
      exact p.accepted
    admitted := p.admitted
  }

def SourceSentence.lower {A : Package} (p : SourceSentence A) :
    Matching.GeneralFixedPoint.Sentence A.base.scope.signature :=
  @CheckedSentence.lower A.base.bindings A.base.scope A.base.literals A.base.literalPrefix p.toChecked

/-- Source satisfaction retains the independent raw interpreter used by the
existing successful checker receipts. -/
def SourceSentence.Satisfies {A : Package}
    (M : @Model A.base.bindings A.base.scope A.base.literalPrefix A.base.literals A.base.hooks)
    (p : SourceSentence A) : Prop :=
  @CheckedSentence.Satisfies A.base.bindings A.base.scope A.base.literals A.base.literalPrefix
    A.base.hooks M p.toChecked

/-- A total action on actual successful receipts. Fuel, module index and
variable names are unchanged; the target success is derived recursively. -/
def SourceSentence.mapStep {A B : Package} (f : Step A B)
    (profiles : literalProfiles A = true) (p : SourceSentence A) : SourceSentence B where
  moduleIndex := p.moduleIndex
  fuel := p.fuel
  sets := mapNames f.semantic.native.sorts p.sets
  objects := mapNames f.semantic.native.sorts p.objects
  sort := f.semantic.native.sorts p.sort
  raw := Surface.raw f.semantic.native.sorts f.names p.raw
  typed := reindexPattern f p.typed
  accepted := f.elaborate_forward profiles p.fuel p.moduleIndex p.sets p.objects
    p.sort p.raw p.typed p.accepted
  admitted := (reindexPattern_admissible f p.typed).trans p.admitted

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
