module

public import Silmaril.Logic.Kore.FixedPoint.Modules.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.FixedPoint
open CategoryTheory Silmaril.Logic.Institution

/-- Lower an actual source presentation, retaining its signature and mapping
its axiom set through the checked syntax translation. -/
def lowerPresentation : Presentation ⥤
    Silmaril.Logic.Institution.Presentation (Matching.FixedPoint.institution String) where
  obj P := ⟨P.sig, Sentence.lower '' P.axioms⟩
  map {P Q} f :=
    { sig := f.sig
      mapsTo := by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨p.map f.sig, f.mapsTo hp, Sentence.lower_map f.sig p⟩ }
  map_id _ := by apply Silmaril.Logic.Institution.Presentation.hom_ext; rfl
  map_comp _ _ := by apply Silmaril.Logic.Institution.Presentation.hom_ext; rfl

namespace Modules
/-- Successful complete-text checking retains exactly the parsed definition. -/
theorem checkText_parsed_source {fuel : Nat} {text : String} {result : CheckedDefinition}
    (h : checkText fuel text = some result) : parse text = some result.source := by
  unfold checkText at h
  cases hp : parse text with
  | none => simp [hp] at h
  | some parsed =>
      have hc : Kore.Modules.Checking.checkDefinitionWith Checking.profile fuel parsed =
          some result := by simpa [hp] using h
      rw [Kore.Modules.Checking.checkDefinition_source hc]
      rfl

variable {ambient : Kore.Modules.Scope}

def nativePresentation (m : CheckedModule ambient) := lowerPresentation.obj m.presentation

def nativeTheory (m : CheckedModule ambient) :=
  (Silmaril.Logic.Institution.Theory.ofPresentation
    (Matching.FixedPoint.institution String)).obj (nativePresentation m)

theorem models_native (m : CheckedModule ambient)
    (M : Matching.FixedPoint.Model ambient.signature) :
    (∀ p ∈ m.axiomSet, Sentence.Satisfies M p) ↔
      ∀ p ∈ (nativePresentation m).axioms, Matching.FixedPoint.Sentence.Satisfies M p := by
  constructor
  · rintro h _ ⟨p, hp, rfl⟩
    exact (Sentence.satisfies_lower M p).mp (h p hp)
  · intro h p hp
    exact (Sentence.satisfies_lower M p).mpr (h _ ⟨p, hp, rfl⟩)

/-- Semantic closure adds exactly the consequences and leaves the models
unchanged, on both sides of the actual theory comparison. -/
theorem theory_models_native (m : CheckedModule ambient)
    (M : Matching.FixedPoint.Model ambient.signature) :
    Silmaril.Logic.Institution.Theory.modelsProperty m.theory.sentences M ↔
      Silmaril.Logic.Institution.Theory.modelsProperty (nativeTheory m).sentences M := by
  have sourceModels := congrArg
    (fun E : Set ((institution.obj ambient.signature).Mod) => M ∈ E)
    ((institution.obj ambient.signature).modelsOf_closure m.axiomSet)
  have nativeModels := congrArg
    (fun E : Set (((Matching.FixedPoint.institution String).obj ambient.signature).Mod) => M ∈ E)
    (((Matching.FixedPoint.institution String).obj ambient.signature).modelsOf_closure
      (nativePresentation m).axioms)
  exact (Iff.of_eq sourceModels).trans
    ((models_native m M).trans (Iff.of_eq nativeModels).symm)

theorem proves_native (m : CheckedModule ambient) (p : Sentence ambient.signature) :
    m.Proves p ↔ ((Matching.FixedPoint.institution String).obj ambient.signature).Entails
      (nativePresentation m).axioms p.lower :=
  entails_iff ambient.signature m.axiomSet p

def nativeImportHom (parent child : CheckedModule ambient)
    (h : parent.asImport ∈ child.imports) : (nativePresentation parent) ⟶ (nativePresentation child) :=
  lowerPresentation.map (Kore.Modules.Checking.CheckedModule.importHom parent child h)

def nativeImportReduct (parent child : CheckedModule ambient)
    (h : parent.asImport ∈ child.imports) : (nativeTheory child).Models ⥤ (nativeTheory parent).Models :=
  Silmaril.Logic.Institution.Theory.reduct
    ((Silmaril.Logic.Institution.Theory.ofPresentation
      (Matching.FixedPoint.institution String)).map (nativeImportHom parent child h))

/-- Translating a composite import is the composite of translated imports. -/
theorem import_square (a b c : CheckedModule ambient)
    (ab : a.asImport ∈ b.imports) (bc : b.asImport ∈ c.imports) :
    lowerPresentation.map
        (Kore.Modules.Checking.CheckedModule.importHom a b ab ≫
          Kore.Modules.Checking.CheckedModule.importHom b c bc) =
      nativeImportHom a b ab ≫ nativeImportHom b c bc := lowerPresentation.map_comp _ _

end Modules
end Silmaril.Logic.Kore.FixedPoint
