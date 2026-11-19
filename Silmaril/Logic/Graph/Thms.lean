module

public import Silmaril.Logic.Graph.Defs
public import Silmaril.Logic.Fragments.Institution.Thms
import Silmaril.Proofs.Logic.Graph.Institution

@[expose] public section
namespace Silmaril.Logic.Graph
open CategoryTheory Silmaril.Logic.Institution

theorem satisfaction {A B : Signature} (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Sat M (sentenceMap f p) ↔ Sat (reduct f M) p := Iff.rfl
theorem present_satisfaction {A B : Signature} (f : A ⟶ B) (M : PresentModel B) (p : PresentSentence A) :
    PresentSat M (presentMap f p) ↔ PresentSat (presentReduct f M) p := by cases p <;> rfl

theorem corridor_id (A : Signature) : corridor (𝟙 A) = 𝟙 (room A) := Proofs.corridor_id A
theorem corridor_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    corridor (f ≫ g) = corridor f ≫ corridor g := Proofs.corridor_comp f g
theorem present_id (A : Signature) : presentCorridor (𝟙 A) = 𝟙 (presentRoom A) := Proofs.present_id A
theorem present_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    presentCorridor (f ≫ g) = presentCorridor f ≫ presentCorridor g := Proofs.present_comp f g

def institution : Signature ⥤ Room.{0,0,0} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

def presenceInstitution : Signature ⥤ Room.{0,0,0} where
  obj := presentRoom
  map := presentCorridor
  map_id := present_id
  map_comp := present_comp

/-- Connectives extend the atomic institution without changing its reducts. -/
def withFragment (F : Fragments.Fragment.{0}) : Signature ⥤ Room.{0,0,0} := F.institution institution

theorem present_wellformed_reduct {A B : Signature} (f : A ⟶ B) (M : PresentModel B)
    (h : M.WellFormed) : (presentReduct f M).WellFormed := fun a b edge => h (f.node a) (f.node b) edge

theorem marker_node {A : Signature} (M : PresentModel A) (a : A.Node) :
    (markPresence M).edge a a ↔ a ∈ M.present := by simp [markPresence]

theorem marker_off_diagonal {A : Signature} (M : PresentModel A) (a b : A.Node) (hne : a ≠ b) :
    (markPresence M).edge a b ↔ M.graph.edge a b := by simp [markPresence, hne]

theorem marker_reindex {A B : Signature} (f : A ⟶ B) (inj : Function.Injective f.node) (M : PresentModel B) :
    markPresence (presentReduct f M) = reduct f (markPresence M) := Proofs.marker_injective f inj M

end Silmaril.Logic.Graph
