module

public import Silmaril.Logic.Kore.Modules.Theory.Defs

@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Checking
open CategoryTheory Silmaril.Logic.Institution
variable {ambient : Scope} {profile : SentenceProfile}

namespace CheckedModule

/-- Exact import/axiom semantics: claims do not occur in this equation. -/
theorem mem_axiomSet (m : CheckedModule ambient profile)
    (p : (profile.institution.obj ambient.signature).Sen) :
    p ∈ m.axiomSet ↔ (∃ d ∈ m.localAxioms, d.sentence = p) ∨
      ∃ parent ∈ m.imports, ∃ d ∈ parent.axioms, d.sentence = p := by
  simp only [axiomSet, axioms, List.mem_append, List.mem_flatMap]
  constructor
  · rintro ⟨d, h | ⟨parent, hp, hd⟩, eq⟩
    · exact Or.inl ⟨d, h, eq⟩
    · exact Or.inr ⟨parent, hp, d, hd, eq⟩
  · rintro (⟨d, hd, eq⟩ | ⟨parent, hp, d, hd, eq⟩)
    · exact ⟨d, Or.inl hd, eq⟩
    · exact ⟨d, Or.inr ⟨parent, hp, hd⟩, eq⟩

/-- A model of the checked presentation satisfies precisely the local axioms and
all imported axiom presentations, including their transitive imports. -/
theorem models_iff (m : CheckedModule ambient profile) (M : (profile.institution.obj ambient.signature).Mod) :
    (∀ p ∈ m.axiomSet, (profile.institution.obj ambient.signature).Sat M p) ↔
      (∀ d ∈ m.localAxioms, (profile.institution.obj ambient.signature).Sat M d.sentence) ∧
      (∀ parent ∈ m.imports, ∀ d ∈ parent.axioms,
        (profile.institution.obj ambient.signature).Sat M d.sentence) := by
  constructor
  · intro h
    constructor
    · intro d hd; exact h _ ((mem_axiomSet _ _).2 (Or.inl ⟨d, hd, rfl⟩))
    · intro parent hp d hd
      exact h _ ((mem_axiomSet _ _).2 (Or.inr ⟨parent, hp, d, hd, rfl⟩))
  · rintro ⟨hl, hi⟩ p hp
    rcases (mem_axiomSet _ _).1 hp with ⟨d, hd, rfl⟩ | ⟨parent, hparent, d, hd, rfl⟩
    · exact hl d hd
    · exact hi parent hparent d hd

/-- Actual syntactic presentation arrow for a resolved import. -/
noncomputable def importHom (parent child : CheckedModule ambient profile)
    (h : parent.asImport ∈ child.imports) : parent.presentation ⟶ child.presentation where
  sig := 𝟙 ambient.signature
  mapsTo := by
    intro p hp
    change (profile.institution.map (𝟙 ambient.signature)).sen p ∈ child.axiomSet
    rw [profile.institution.map_id]
    change p ∈ child.axiomSet
    rcases hp with ⟨d, hd, eq⟩
    exact (mem_axiomSet _ _).2 (Or.inr ⟨parent.asImport, h, d, hd, eq⟩)

/-- The same import induces a genuine arrow between semantically closed theories. -/
noncomputable def importTheoryHom (parent child : CheckedModule ambient profile)
    (h : parent.asImport ∈ child.imports) : parent.theory ⟶ child.theory :=
  (Theory.ofPresentation profile.institution).map (importHom parent child h)

/-- The shared theory machinery supplies the model category and reduct functor. -/
noncomputable def importReduct (parent child : CheckedModule ambient profile)
    (h : parent.asImport ∈ child.imports) : child.theory.Models ⥤ parent.theory.Models :=
  Theory.reduct (importTheoryHom parent child h)

/-- Diamond imports commute as actual presentation arrows, retaining common symbols. -/
theorem import_diamond (a b c d : CheckedModule ambient profile)
    (ab : a.asImport ∈ b.imports) (ac : a.asImport ∈ c.imports)
    (bd : b.asImport ∈ d.imports) (cd : c.asImport ∈ d.imports) :
    importHom a b ab ≫ importHom b d bd = importHom a c ac ≫ importHom c d cd := by
  apply Presentation.hom_ext
  rfl

/-- Theory import composition respects the same diamond equation. -/
theorem importTheory_diamond (a b c d : CheckedModule ambient profile)
    (ab : a.asImport ∈ b.imports) (ac : a.asImport ∈ c.imports)
    (bd : b.asImport ∈ d.imports) (cd : c.asImport ∈ d.imports) :
    importTheoryHom a b ab ≫ importTheoryHom b d bd =
      importTheoryHom a c ac ≫ importTheoryHom c d cd := by
  apply Theory.hom_ext
  rfl

/-- Consequence proved using an imported module remains valid in its importer. -/
theorem proves_import (parent child : CheckedModule ambient profile)
    (h : parent.asImport ∈ child.imports) (p : (profile.institution.obj ambient.signature).Sen)
    (proof : parent.Proves p) : child.Proves p := by
  change ∀ (M : (profile.institution.obj ambient.signature).Mod),
    (∀ p ∈ child.axiomSet, (profile.institution.obj ambient.signature).Sat M p) →
      (profile.institution.obj ambient.signature).Sat M p
  intro M hM
  apply proof M
  intro q hq
  rcases hq with ⟨d, hd, eq⟩
  exact hM q ((mem_axiomSet _ _).2 (Or.inr ⟨parent.asImport, h, d, hd, eq⟩))

end CheckedModule

/-- Every declaration in a checked module passed its actual source visibility,
alias/profile and intrinsic elaboration check at the recorded fuel. -/
theorem declarations_valid (m : CheckedModule ambient profile) :
    ∀ d ∈ m.source.declarations,
      validateDeclarationWith profile ambient m.scope m.fuel d.declaration = true :=
  List.all_eq_true.mp m.validated

/-- The checker retains the very definition it checked. -/
theorem checkDefinition_source {fuel : Nat} {d : Definition profile.Raw}
    {result : CheckedDefinition profile}
    (h : checkDefinitionWith profile fuel d = some result) : result.source = d := by
  unfold checkDefinitionWith at h
  obtain ⟨⟨ambient, ms⟩, _, eq⟩ := Option.bind_eq_some_iff.mp h
  cases eq
  rfl

/-- The checked text API really runs the complete source reader. -/
theorem checkText_source {fuel : Nat} {text : String} {result : CheckedDefinition}
    (h : checkText fuel text = some result) :
    ∃ parsed, Syntax.parse text = some parsed ∧ checkDefinition fuel parsed = some result := by
  unfold checkText at h
  cases hp : Syntax.parse text with
  | none => simp [hp] at h
  | some parsed => exact ⟨parsed, rfl, by simpa [hp] using h⟩

/-- Source binding includes the retained definition, not an unrelated parsed AST. -/
theorem checkText_parsed_source {fuel : Nat} {text : String} {result : CheckedDefinition}
    (h : checkText fuel text = some result) : Syntax.parse text = some result.source := by
  rcases checkText_source h with ⟨parsed, hp, hc⟩
  rw [checkDefinition_source hc]
  exact hp

end Silmaril.Logic.Kore.Modules.Checking

namespace Silmaril.Logic.Kore.Modules.Scope
open CategoryTheory

theorem inclusion_id (scope : Scope) : inclusion (a := scope) (fun _ h => h) = 𝟙 scope.signature := by
  apply Algebraic.ManySorted.Signature.Hom.ext String
  intros
  rfl

theorem inclusion_comp {a b c : Scope} (ab : a.symbols ⊆ b.symbols) (bc : b.symbols ⊆ c.symbols) :
    inclusion ab ≫ inclusion bc = inclusion (fun _ h => bc (ab h)) := by
  apply Algebraic.ManySorted.Signature.Hom.ext String
  intros
  rfl

theorem inclusion_satisfaction {a b : Scope} (ab : a.symbols ⊆ b.symbols)
    (M : Matching.FirstOrder.Model b.signature) (p : FirstOrder.Sentence a.signature) :
    FirstOrder.Sentence.Satisfies M (p.map (inclusion ab)) ↔
      FirstOrder.Sentence.Satisfies (Matching.FirstOrder.SignatureMap.reduct (inclusion ab) M) p :=
  FirstOrder.Sentence.satisfaction (inclusion ab) M p
end Silmaril.Logic.Kore.Modules.Scope
