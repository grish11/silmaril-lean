module

public import Silmaril.Logic.Graph.Incidence.Defs
import Silmaril.Proofs.Logic.Graph.Incidence

@[expose] public section
namespace Silmaril.Logic.Graph.Incidence
open CategoryTheory Silmaril.Logic.Institution

theorem satisfaction {A B : Signature} (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Sat M (sentenceMap f p) ↔ Sat (reduct f M) p := Proofs.satisfaction f M p

def room (A : Signature) : Room.{0,0,0} :=
  ⟨Sentence A, Cat.of (Discrete (Model A)), fun M p => Sat (Discrete.as M) p⟩

def corridor {A B : Signature} (f : A ⟶ B) : room A ⟶ room B :=
  ⟨sentenceMap f, Discrete.functor fun M => Discrete.mk (reduct f M), fun M p => satisfaction f (Discrete.as M) p⟩

theorem corridor_id (A : Signature) : corridor (𝟙 A) = 𝟙 (room A) := by
  apply Room.hom_ext
  · funext p; cases p <;> rfl
  · exact Functor.ext (fun M => by cases M; rfl) (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)

theorem corridor_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    corridor (f ≫ g) = corridor f ≫ corridor g := by
  apply Room.hom_ext
  · funext p; cases p <;> rfl
  · exact Functor.ext (fun _ => rfl) (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)

/-- Incidence is signature data. `sourceKnown` and `targetKnown` observe its
partiality; endpoint-equality sentences are deliberately not claimed natural
under noninjective node renamings. -/
def institution : Signature ⥤ Room.{0,0,0} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

theorem wellformed_reduct {A B : Signature} (f : A ⟶ B) (M : Model B) (h : M.WellFormed) :
    (reduct f M).WellFormed := Proofs.wf_reduct f M h

theorem complete_reduct {A B : Signature} (f : A ⟶ B) (M : Model B) (h : M.Complete) :
    (reduct f M).Complete := fun e he =>
  ⟨(satisfaction f M (.sourceKnown e)).mp (h (f.edge e) he).1,
    (satisfaction f M (.targetKnown e)).mp (h (f.edge e) he).2⟩

theorem total_complete (A : TotalSignature) (M : Model A.toOptional) : M.Complete :=
  fun _ _ => ⟨rfl, rfl⟩

/-- Forgetting edge identities always preserves edges forward. -/
theorem relation_forward {A B : Signature} (f : A ⟶ B) (M : Model B) {a b : A.Node}
    (h : (reduct f M).relation.edge a b) : M.relation.edge (f.node a) (f.node b) :=
  Proofs.relation_forward f M h

/-- Exact relational reduct needs endpoint reflection and edge coverage. -/
theorem relation_iff {A B : Signature} (f : A ⟶ B) (M : Model B)
    (nodes : Function.Injective f.node) (edges : Function.Surjective f.edge) (a b : A.Node) :
    (reduct f M).relation.edge a b ↔ M.relation.edge (f.node a) (f.node b) :=
  Proofs.relation_iff f M nodes edges a b

end Silmaril.Logic.Graph.Incidence
