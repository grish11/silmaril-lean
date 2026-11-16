module

public import Silmaril.Logic.FirstOrder.FiniteLists.Defs
import Silmaril.Proofs.Logic.FirstOrder.FiniteLists

@[expose] public section
namespace Silmaril.Logic.FirstOrder.FiniteLists
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

@[simp] theorem publicMap_id (S : Signature) : publicMap (𝟙 S) = 𝟙 (publicSignature S) :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.publicMap_id S

@[simp] theorem publicMap_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) :
    publicMap (f ≫ g) = publicMap f ≫ publicMap g :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.publicMap_comp f g

theorem listReduct_reduct {S T : Signature} (f : S ⟶ T)
    (M : FOL.Structure (publicSignature T)) :
    listReduct ((FOL.Structure.reduct (publicMap f)).obj M) = listReduct M :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.listReduct_reduct f M

theorem isFree_reduct {S T : Signature} (f : S ⟶ T)
    (M : FOL.Structure (publicSignature T)) (h : IsFree M) :
    IsFree ((FOL.Structure.reduct (publicMap f)).obj M) :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.isFree_reduct f M h

theorem fold_natural {S : Signature} {M N : FOL.Structure (publicSignature S)}
    (h : M ⟶ N) (xs : List (M.carrier .discourse)) :
    h.map .sequence (List.foldr (listReduct M).cons (listReduct M).nil xs) =
      List.foldr (listReduct N).cons (listReduct N).nil (xs.map (h.map .discourse)) :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.fold_natural h xs

theorem evaluation_natural {S : Signature} (M N : Model S)
    (h : M.obj ⟶ N.obj) (xs : List (M.obj.carrier .discourse)) :
    h.map .sequence (evaluationEquiv M xs) =
      evaluationEquiv N (xs.map (h.map .discourse)) :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.evaluation_natural M N h xs

theorem NativeModel.evaluation {S : Signature} (M : NativeModel S)
    (xs : List M.Discourse) : evaluationEquiv M.toModel xs = xs :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.native_evaluation M xs

/-- The inverse evaluation map is also the identity on canonical native lists. -/
theorem NativeModel.evaluation_symm {S : Signature} (M : NativeModel S)
    (xs : List M.Discourse) : (evaluationEquiv M.toModel).symm xs = xs := by
  exact ((evaluationEquiv M.toModel).symm_apply_eq).2 (M.evaluation xs).symm

theorem reduct_id (S : Signature) : reduct (𝟙 S) = 𝟭 (Model S) :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.reduct_id S

theorem reduct_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) :
    reduct (f ≫ g) = reduct g ⋙ reduct f :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.reduct_comp f g

theorem corridor_id (S : Signature) : corridor (𝟙 S) = 𝟙 (room S) :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.corridor_id S

theorem corridor_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) :
    corridor (f ≫ g) = corridor f ≫ corridor g :=
  Silmaril.Proofs.Logic.FirstOrder.FiniteLists.corridor_comp f g

def publicSignatures : Signature ⥤ FOL.Signature where
  obj := publicSignature
  map := publicMap
  map_id := publicMap_id
  map_comp := publicMap_comp

/-- Independent full-sentence FOL with actual finite-list model semantics. -/
def institution : Signature ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id := corridor_id
  map_comp := corridor_comp

def inst : Inst.{1,0,0,0,1} := ⟨Signature, institution⟩

end Silmaril.Logic.FirstOrder.FiniteLists
