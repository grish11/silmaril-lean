module

public import Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution.Defs

public section
namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EqualityInstitution
open Silmaril.Logic.TypeTheory.LambdaPi
open Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution
open CategoryTheory

theorem sentence_identity (P : TypedPresentation) (q : Sentence) :
    q.map (𝟙 P) = q := by
  cases q
  simp only [Sentence.map, show (𝟙 P : P ⟶ P).toConstantAssignment =
    ConstantAssignment.identity from rfl, ConstantAssignment.term_identity]

theorem sentence_comp {P Q R : TypedPresentation} (F : P ⟶ Q) (G : Q ⟶ R) (q : Sentence) :
    q.map (F ≫ G) = (q.map F).map G := by
  cases q
  simp only [Sentence.map, show (F ≫ G).toConstantAssignment =
    F.toConstantAssignment.comp G.toConstantAssignment from rfl, ConstantAssignment.term_comp]

theorem holds_map {P Q : TypedPresentation} (F : P ⟶ Q) {q : Sentence}
    (h : Holds P q) : Holds Q (q.map F) := by
  obtain ⟨hl, hr, hc⟩ := h
  refine ⟨?_, ?_, F.map_conversion hc⟩
  · simpa only [Set.image_empty, ConstantAssignment.judgment, List.map_nil, Sentence.map] using F.map_derives hl
  · simpa only [Set.image_empty, ConstantAssignment.judgment, List.map_nil, Sentence.map] using F.map_derives hr

theorem satisfaction {P Q : TypedPresentation} (F : P ⟶ Q) (M : Model Q) (q : Sentence) :
    M.Satisfies (q.map F) ↔ (M.reduce F).Satisfies q := by
  change Holds M.target ((q.map F).map M.assignment) ↔ Holds M.target (q.map (F ≫ M.assignment))
  rw [sentence_comp]

theorem valid_iff (P : TypedPresentation) (q : Sentence) :
    (∀ M : Model P, M.Satisfies q) ↔ Holds P q := by
  refine ⟨?_, fun h M => holds_map M.assignment h⟩
  intro h
  have hid := h (Model.identity P)
  change Holds P (q.map (𝟙 P)) at hid
  rw [sentence_identity] at hid
  exact hid

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EqualityInstitution
