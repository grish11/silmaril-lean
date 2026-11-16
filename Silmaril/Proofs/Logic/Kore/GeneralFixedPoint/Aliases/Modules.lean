module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Modules.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Aliases
open CategoryTheory Silmaril.Logic.Institution

/-- Lower an actual source presentation, retaining its signature and mapping
its axiom set through the checked syntax translation. -/
def lowerPresentation : Presentation ⥤
    Silmaril.Logic.Institution.Presentation (Matching.GeneralFixedPoint.institution String) where
  obj P := ⟨P.sig, Sentence.lower '' P.axioms⟩
  map {P Q} f :=
    { sig := f.sig
      mapsTo := by
        rintro _ ⟨p, hp, rfl⟩
        exact ⟨p.map f.sig, f.mapsTo hp, Sentence.lower_map f.sig p⟩ }
  map_id _ := by apply Silmaril.Logic.Institution.Presentation.hom_ext; rfl
  map_comp _ _ := by apply Silmaril.Logic.Institution.Presentation.hom_ext; rfl

namespace Checking
namespace CheckedModule
variable {ambient : Kore.Modules.Scope}

/-- Imports induce real source presentation arrows, using retained axiom identity. -/
def importHom (parent child : CheckedModule ambient)
    (h : parent.asImport ∈ child.imports) : parent.presentation ⟶ child.presentation where
  sig := 𝟙 ambient.signature
  mapsTo := by
    intro p hp
    change (institution.map (𝟙 ambient.signature)).sen p ∈ child.axiomSet
    rw [institution.map_id]
    change p ∈ child.axiomSet
    obtain ⟨d, hd, eq⟩ := hp
    refine ⟨d, ?_, eq⟩
    change d ∈ child.localAxioms ++ child.imports.flatMap Import.axioms
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨parent.asImport, h, hd⟩)
end CheckedModule

theorem checkDefinition_source {fuel : Nat} {d : SourceDefinition}
    {result : Checking.CheckedDefinition}
    (h : checkDefinition fuel d = some result) : result.source = d := by
  unfold checkDefinition at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · obtain ⟨ms, _, eq⟩ := Option.bind_eq_some_iff.mp h
      cases eq
      rfl
end Checking

namespace Modules
open Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Checking
/-- Successful complete-text checking retains exactly the parsed definition. -/
theorem checkText_parsed_source {fuel : Nat} {text : String} {result : Checking.CheckedDefinition}
    (h : checkText fuel text = some result) : parse text = some result.source := by
  unfold checkText at h
  cases hp : parse text with
  | none => simp [hp] at h
  | some parsed =>
      have hc : Checking.checkDefinition fuel parsed =
          some result := by simpa [hp] using h
      rw [Checking.checkDefinition_source hc]

variable {ambient : Kore.Modules.Scope}

def nativePresentation (m : CheckedModule ambient) := lowerPresentation.obj m.presentation

def nativeTheory (m : CheckedModule ambient) :=
  (Silmaril.Logic.Institution.Theory.ofPresentation
    (Matching.GeneralFixedPoint.institution String)).obj (nativePresentation m)

theorem models_native (m : CheckedModule ambient)
    (M : Matching.GeneralFixedPoint.Model ambient.signature) :
    (∀ p ∈ m.axiomSet, Sentence.Satisfies M p) ↔
      ∀ p ∈ (nativePresentation m).axioms, Matching.GeneralFixedPoint.Sentence.Satisfies M p := by
  constructor
  · rintro h _ ⟨p, hp, rfl⟩
    exact (Sentence.satisfies_lower M p).mp (h p hp)
  · intro h p hp
    exact (Sentence.satisfies_lower M p).mpr (h _ ⟨p, hp, rfl⟩)

/-- Semantic closure adds exactly the consequences and leaves the models
unchanged, on both sides of the actual theory comparison. -/
theorem theory_models_native (m : CheckedModule ambient)
    (M : Matching.GeneralFixedPoint.Model ambient.signature) :
    Silmaril.Logic.Institution.Theory.modelsProperty m.theory.sentences M ↔
      Silmaril.Logic.Institution.Theory.modelsProperty (nativeTheory m).sentences M := by
  have sourceModels := congrArg
    (fun E : Set ((institution.obj ambient.signature).Mod) => M ∈ E)
    ((institution.obj ambient.signature).modelsOf_closure m.axiomSet)
  have nativeModels := congrArg
    (fun E : Set (((Matching.GeneralFixedPoint.institution String).obj ambient.signature).Mod) => M ∈ E)
    (((Matching.GeneralFixedPoint.institution String).obj ambient.signature).modelsOf_closure
      (nativePresentation m).axioms)
  exact (Iff.of_eq sourceModels).trans
    ((models_native m M).trans (Iff.of_eq nativeModels).symm)

theorem proves_native (m : CheckedModule ambient) (p : Sentence ambient.signature) :
    m.Proves p ↔ ((Matching.GeneralFixedPoint.institution String).obj ambient.signature).Entails
      (nativePresentation m).axioms p.lower :=
  entails_iff ambient.signature m.axiomSet p

def nativeImportHom (parent child : CheckedModule ambient)
    (h : parent.asImport ∈ child.imports) : (nativePresentation parent) ⟶ (nativePresentation child) :=
  lowerPresentation.map (Checking.CheckedModule.importHom parent child h)

def nativeImportReduct (parent child : CheckedModule ambient)
    (h : parent.asImport ∈ child.imports) : (nativeTheory child).Models ⥤ (nativeTheory parent).Models :=
  Silmaril.Logic.Institution.Theory.reduct
    ((Silmaril.Logic.Institution.Theory.ofPresentation
      (Matching.GeneralFixedPoint.institution String)).map (nativeImportHom parent child h))

/-- Translating a composite import is the composite of translated imports. -/
theorem import_square (a b c : CheckedModule ambient)
    (ab : a.asImport ∈ b.imports) (bc : b.asImport ∈ c.imports) :
    lowerPresentation.map
        (Checking.CheckedModule.importHom a b ab ≫
          Checking.CheckedModule.importHom b c bc) =
      nativeImportHom a b ab ≫ nativeImportHom b c bc := lowerPresentation.map_comp _ _

end Modules
end Silmaril.Logic.Kore.GeneralFixedPoint.Aliases
