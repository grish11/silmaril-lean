module

public import Silmaril.Logic.Graph.Defs

@[expose] public section
namespace Silmaril.Logic.Graph.Proofs
open CategoryTheory Silmaril.Logic.Institution

theorem corridor_id (A : Signature) : corridor (𝟙 A) = 𝟙 (room A) := by
  apply Room.hom_ext
  · rfl
  · exact Functor.ext (fun _ => rfl) (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)
theorem corridor_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    corridor (f ≫ g) = corridor f ≫ corridor g := by
  apply Room.hom_ext
  · rfl
  · exact Functor.ext (fun _ => rfl) (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)

theorem present_id (A : Signature) : presentCorridor (𝟙 A) = 𝟙 (presentRoom A) := by
  apply Room.hom_ext
  · funext p; cases p <;> rfl
  · exact Functor.ext (fun M => by cases M; rfl) (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)
theorem present_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    presentCorridor (f ≫ g) = presentCorridor f ≫ presentCorridor g := by
  apply Room.hom_ext
  · funext p; cases p <;> rfl
  · exact Functor.ext (fun _ => rfl) (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)

theorem marker_injective {A B : Signature} (f : A ⟶ B) (inj : Function.Injective f.node)
    (M : PresentModel B) : markPresence (presentReduct f M) = reduct f (markPresence M) := by
  change (⟨_⟩ : Silmaril.Semantics.Graph.RelGraph A.Node) = ⟨_⟩
  congr 1
  funext a b
  apply propext
  simp only [markPresence, presentReduct, reduct, Set.mem_preimage]
  simp only [ne_eq, inj.eq_iff]

end Silmaril.Logic.Graph.Proofs
