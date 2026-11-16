module

public import Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EqualityInstitution

public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution
open CategoryTheory Silmaril.Logic.Institution

/-- Actual native encodings preserve both typings and conversion. -/
theorem Holds.map {P Q : TypedPresentation} (F : P ⟶ Q) {q : Sentence}
    (h : Holds P q) : Holds Q (q.map F) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EqualityInstitution.holds_map F h

/-- Encoding composition gives exact satisfaction under model reduction. -/
theorem Model.satisfaction {P Q : TypedPresentation} (F : P ⟶ Q) (M : Model Q) (q : Sentence) :
    M.Satisfies (q.map F) ↔ (M.reduce F).Satisfies q :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EqualityInstitution.satisfaction F M q

def corridor {P Q : TypedPresentation} (F : P ⟶ Q) : room P ⟶ room Q where
  sen := Sentence.map F
  mod := Discrete.functor (fun M => Discrete.mk (M.reduce F))
  sat M q := M.as.satisfaction F q

/-- Typed presentations and actual encodings index native equality rooms. -/
def institution : TypedPresentation ⥤ Room.{0, 0, 0} where
  obj := room
  map := corridor
  map_id P := by
    apply Room.hom_ext
    · funext q
      exact Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EqualityInstitution.sentence_identity P q
    · apply Discrete.functor_ext
      intro M
      rfl
  map_comp F G := by
    apply Room.hom_ext
    · funext q
      exact Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EqualityInstitution.sentence_comp F G q
    · apply Discrete.functor_ext
      intro M
      change Discrete.mk (Model.reduce (F ≫ G) M) =
        Discrete.mk (Model.reduce F (Model.reduce G M))
      apply congrArg Discrete.mk
      change Model.mk M.target ((F ≫ G) ≫ M.assignment) =
        Model.mk M.target (F ≫ G ≫ M.assignment)
      rw [Category.assoc]

/-- `institution` as a bundled `Inst`, named so that records and comorphisms can refer to it. -/
def inst := (⟨TypedPresentation, institution⟩ : Silmaril.Logic.Institution.Inst)

/-- One native equality institution over all actual typed presentations. -/
def bundled : Inst.{0, 0, 0, 0, 0} := ⟨TypedPresentation, institution⟩

/-- Fixed-presentation institutions and their actual encoding comorphisms. -/
noncomputable def institutions : TypedPresentation ⥤ CoIns.{0, 0, 0, 0, 0} :=
  institution ⋙ Silmaril.Logic.Institution.Syntactic.roomsToInstitutions

/-- The Hets family uses the existing category of genuine typed native encodings. -/
noncomputable def hets : LogicGraph.{0, 0, 0, 0, 0, 0, 0} :=
  IndexedCoInst.toLogicGraph institutions

end Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution

namespace Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution
open CategoryTheory

/-- Native facts are true under every actual encoding interpretation. -/
theorem sound {P : TypedPresentation} {q : Sentence} (h : Holds P q) (M : Model P) :
    M.Satisfies q := h.map M.assignment

/-- The identity model detects exactly native typing plus conversion. -/
theorem valid_iff (P : TypedPresentation) (q : Sentence) :
    (∀ M : Model P, M.Satisfies q) ↔ Holds P q :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EqualityInstitution.valid_iff P q

end Silmaril.Logic.TypeTheory.LambdaPi.EqualityInstitution
