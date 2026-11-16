module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Paths.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
open CategoryTheory Silmaril.Logic.Institution

theorem SourceSentence.mapPath_append {A B : Package} (path : Path A B) :
    ∀ {C : Package} (next : Path B C) (valid : literalProfiles A = true) (p : SourceSentence A),
    p.mapPath (path.append next) valid =
      (p.mapPath path valid).mapPath next (path.literalProfiles_forward valid) := by
  induction path with
  | nil => intro C next valid p; rfl
  | cons f tail ih =>
      intro C next valid p
      exact ih next (f.literalProfiles_forward valid) (p.mapStep f valid)

/-- The raw component is exactly the existing structural path action. -/
theorem SourceSentence.mapPath_raw {A B : Package} (path : Path A B) :
    ∀ (valid : literalProfiles A = true) (p : SourceSentence A),
    (p.mapPath path valid).raw = path.action p.raw := by
  induction path with
  | nil => intro valid p; rfl
  | cons f tail ih =>
      intro valid p
      exact ih (f.literalProfiles_forward valid) (p.mapStep f valid)

/-- Lowering commutes with every path, not only one structural step. -/
theorem SourceSentence.mapPath_lower {A B : Package} (path : Path A B) :
    ∀ (valid : literalProfiles A = true) (p : SourceSentence A),
    (p.mapPath path valid).lower =
      Matching.SortMaps.Hom.generalSentence path.semantic.native p.lower := by
  induction path with
  | nil A =>
      intro valid p
      exact (Matching.SortMaps.Hom.generalSentence_id (A := A.base.native) p.lower).symm
  | cons f tail ih =>
      intro valid p
      change ((p.mapStep f valid).mapPath tail (f.literalProfiles_forward valid)).lower =
        Matching.SortMaps.Hom.generalSentence (f.semantic.native ≫ tail.semantic.native) p.lower
      rw [ih, SourceSentence.mapStep_lower]
      exact (Matching.SortMaps.Hom.generalSentence_comp f.semantic.native tail.semantic.native p.lower).symm

/-- Raw-source satisfaction follows from the actual checker receipt, its exact
lower/native equation, and the restricted builtin-model reduct. -/
theorem SourceSentence.mapPath_satisfies {A B : Package} (path : Path A B)
    (valid : literalProfiles A = true)
    (M : @Model B.base.bindings B.base.scope B.base.literalPrefix B.base.literals B.base.hooks)
    (p : SourceSentence A) :
    (p.mapPath path valid).Satisfies M ↔ p.Satisfies (Hom.reduct path.semantic M) := by
  calc
    (p.mapPath path valid).Satisfies M ↔
        Matching.GeneralFixedPoint.Sentence.Satisfies
          (@Model.native B.base.bindings _ _ _ _ M) (p.mapPath path valid).lower :=
      (p.mapPath path valid).satisfies_lower M
    _ ↔ Matching.GeneralFixedPoint.Sentence.Satisfies
          (@Model.native A.base.bindings _ _ _ _ (Hom.reduct path.semantic M)) p.lower := by
      rw [p.mapPath_lower path valid]
      exact nativeSatisfaction path.semantic M p.lower
    _ ↔ p.Satisfies (Hom.reduct path.semantic M) :=
      (p.satisfies_lower (Hom.reduct path.semantic M)).symm

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
