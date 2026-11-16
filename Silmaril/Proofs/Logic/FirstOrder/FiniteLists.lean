module

public import Silmaril.Logic.FirstOrder.FiniteLists.Defs

@[expose] public section
namespace Silmaril.Proofs.Logic.FirstOrder.FiniteLists
universe u u' v v'
open CategoryTheory
open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured.Constraints
open Silmaril.Logic.FirstOrder.FiniteLists
open Silmaril.Logic.Institution.Structured.Constraints.Applications

/-- Any FOL homomorphism commutes with evaluation of every actual finite list.
This proof needs constructor preservation only, not injectivity or surjectivity. -/
theorem fold_natural {S : Signature} {M N : FOL.Structure (publicSignature S)}
    (h : M ⟶ N) (xs : List (M.carrier .discourse)) :
    h.map .sequence (List.foldr (listReduct M).cons (listReduct M).nil xs) =
      List.foldr (listReduct N).cons (listReduct N).nil (xs.map (h.map .discourse)) := by
  induction xs with
  | nil => exact (listHom h).map_nil
  | cons x xs ih =>
    exact ((listHom h).map_cons x
      (List.foldr (listReduct M).cons (listReduct M).nil xs)).trans
      (congrArg ((listReduct N).cons (h.map .discourse x)) ih)

/-- Renaming client symbols fixes the entire list algebra, so freeness is
stable under the public FOL reduct. -/
theorem listReduct_reduct {S T : Signature} (f : Signature.Hom S T)
    (M : FOL.Structure (publicSignature T)) :
    listReduct ((FOL.Structure.reduct (publicMap f)).obj M) = listReduct M := rfl

theorem isFree_reduct {S T : Signature} (f : Signature.Hom S T)
    (M : FOL.Structure (publicSignature T)) (h : IsFree M) :
    IsFree ((FOL.Structure.reduct (publicMap f)).obj M) := h

/-- The list equivalence commutes with every original FOL model arrow. -/
theorem evaluation_natural {S : Signature} (M N : Model S)
    (h : M.obj ⟶ N.obj) (xs : List (M.obj.carrier .discourse)) :
    h.map .sequence (evaluationEquiv M xs) =
      evaluationEquiv N (xs.map (h.map .discourse)) := by
  rw [evaluationEquiv_apply, evaluationEquiv_apply]
  exact fold_natural h xs

/-- Canonical native-list expansion evaluates every finite list identically. -/
theorem native_evaluation {S : Signature} (M : NativeModel S)
    (xs : List M.Discourse) : evaluationEquiv (M.toModel) xs = xs := by
  change List.foldr List.cons [] xs = xs
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

theorem publicMap_id (S : Signature) : publicMap (𝟙 S) = 𝟙 (publicSignature S) := by
  have h : (fun {n : Nat} {w : Fin n → ListSort} {s : ListSort} (o : Operation S n w s) =>
      Operation.map (𝟙 S) o) =
      (fun {n : Nat} {w : Fin n → ListSort} {s : ListSort} (o : Operation S n w s) => o) := by
    funext n w s o
    cases o <;> rfl
  exact congrArg
    (fun ops => ({ sorts := id, ops := ops, rels := fun r => r } :
      FOL.Signature.Hom (publicSignature S) (publicSignature S))) h

theorem publicMap_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) :
    publicMap (f ≫ g) = publicMap f ≫ publicMap g := by
  have h : (fun {n : Nat} {w : Fin n → ListSort} {s : ListSort} (o : Operation S n w s) =>
      Operation.map (f ≫ g) o) =
      (fun {n : Nat} {w : Fin n → ListSort} {s : ListSort} (o : Operation S n w s) =>
        Operation.map g (Operation.map f o)) := by
    funext n w s o
    cases o <;> rfl
  exact congrArg
    (fun ops => ({ sorts := id, ops := ops, rels := fun r => g.rels (f.rels r) } :
      FOL.Signature.Hom (publicSignature S) (publicSignature U))) h

/-- Equality of full-subcategory functors can be checked after forgetting the
property proof. This avoids rewriting through a dependent lift proof field. -/
private theorem fullSubcategory_functor_ext {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v'} D]
    (Q : ObjectProperty D) {F G : C ⥤ Q.FullSubcategory}
    (h : F ⋙ Q.ι = G ⋙ Q.ι) : F = G := by
  have hobj : ∀ X, F.obj X = G.obj X := fun X =>
    ObjectProperty.FullSubcategory.ext (congrArg (fun K => K.obj X) h)
  refine CategoryTheory.Functor.ext hobj ?_
  intro X Y f
  apply Q.ι.map_injective
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using
    Functor.congr_hom h f

theorem reduct_id (S : Signature) : reduct (𝟙 S) = 𝟭 (Model S) := by
  apply fullSubcategory_functor_ext (IsFree (S := S))
  change (IsFree (S := S)).ι ⋙ FOL.Structure.reduct (publicMap (𝟙 S)) =
    (IsFree (S := S)).ι
  rw [publicMap_id]
  rfl

theorem reduct_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) :
    reduct (f ≫ g) = reduct g ⋙ reduct f := by
  apply fullSubcategory_functor_ext (IsFree (S := S))
  change (IsFree (S := U)).ι ⋙ FOL.Structure.reduct (publicMap (f ≫ g)) =
    ((IsFree (S := U)).ι ⋙ FOL.Structure.reduct (publicMap g)) ⋙
      FOL.Structure.reduct (publicMap f)
  rw [publicMap_comp]
  rfl

theorem corridor_id (S : Signature) : corridor (𝟙 S) = 𝟙 (room S) := by
  apply Silmaril.Logic.Institution.Room.hom_ext
  · funext p
    change FOL.Sentence.map (publicMap (𝟙 S)) p = p
    rw [publicMap_id]
    exact FOL.Sentence.map_id p
  · exact reduct_id S

theorem corridor_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U) :
    corridor (f ≫ g) = corridor f ≫ corridor g := by
  apply Silmaril.Logic.Institution.Room.hom_ext
  · funext p
    change FOL.Sentence.map (publicMap (f ≫ g)) p =
      FOL.Sentence.map (publicMap g) (FOL.Sentence.map (publicMap f) p)
    rw [publicMap_comp]
    exact FOL.Sentence.map_comp (publicMap f) (publicMap g) p
  · exact reduct_comp f g

end Silmaril.Proofs.Logic.FirstOrder.FiniteLists
