module

public import Silmaril.Logic.Matching.GuardedFOL.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

private theorem signature_hom_ext {A B : SortMaps.Signature} (f g : A ⟶ B)
    (hs : f.sorts = g.sorts)
    (ho : ∀ n inputs output op, HEq (@f.operations n inputs output op) (@g.operations n inputs output op)) : f = g := by
  cases f with | mk sf of =>
  cases g with | mk sg og =>
  cases hs
  have h : @of = @og := by
    funext n inputs output op
    exact eq_of_heq (ho n inputs output op)
  cases h
  rfl

theorem signatureMap_id (S : FOL.Signature) : signatureMap (𝟙 S) = 𝟙 (signature S) := by
  apply signature_hom_ext
  · funext s
    cases s <;> rfl
  · intro n inputs output op
    cases op <;> rfl

theorem signatureMap_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    signatureMap (f ≫ g) = signatureMap f ≫ signatureMap g := by
  apply signature_hom_ext
  · funext s
    cases s <;> rfl
  · intro n inputs output op
    cases op <;> rfl

def signatures : FOL.Signature ⥤ SortMaps.Signature where
  obj := signature
  map := signatureMap
  map_id := signatureMap_id
  map_comp := signatureMap_comp

/-- Arrows are actual homomorphisms of decoded public FOL structures.
No arbitrary matching-pattern invariance along these arrows is asserted. -/
instance (S : FOL.Signature) : Category (Model S) where
  Hom M N := FOL.Structure.Hom (decode M) (decode N)
  id _ := ⟨fun _ x => x, fun _ _ => rfl, fun _ _ h => h⟩
  comp f g := ⟨fun s x => g.map s (f.map s x), fun op args => by rw [f.map_op, g.map_op],
    fun {_ inputs} r args h => g.map_rel r _ (f.map_rel r args h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

def decodeFunctor (S : FOL.Signature) : Model S ⥤ FOL.Structure S where
  obj := decode
  map h := h

@[ext] theorem Model.ext {S : FOL.Signature} (M N : Model S) (h : M.base = N.base) : M = N := by
  cases M; cases N; cases h; rfl

def reduct {S T : FOL.Signature} (f : S ⟶ T) (M : Model T) : Model S where
  base := SortMaps.Hom.reduct (signatureMap f) M.base
  function op args := M.function (f.ops op) args
  relation r args := M.relation (f.rels r) args
  definedness s args := M.definedness (f.sorts s) args
  truth args := M.truth args

/-- Decoding the actual graph reduct is exactly the public FOL reduct. -/
theorem decode_reduct {S T : FOL.Signature} (f : S ⟶ T) (M : Model T) :
    decode (reduct f M) = (FOL.Structure.reduct f).obj (decode M) := rfl

def reductFunctor {S T : FOL.Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj := reduct f
  map h := (FOL.Structure.reduct f).map h

theorem reduct_id {S : FOL.Signature} (M : Model S) : reduct (𝟙 S) M = M := by
  apply Model.ext
  change SortMaps.Hom.reduct (signatureMap (𝟙 S)) M.base = _
  rw [signatureMap_id, SortMaps.Hom.reduct_id]

theorem reduct_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) (M : Model U) :
    reduct (f ≫ g) M = reduct f (reduct g M) := by
  apply Model.ext
  change SortMaps.Hom.reduct (signatureMap (f ≫ g)) M.base = _
  rw [signatureMap_comp, SortMaps.Hom.reduct_comp]
  rfl

private theorem model_hom_hext {S : FOL.Signature} {M M' N N' : Model S}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N') (h : HEq f.map g.map) : HEq f g := by
  cases hM; cases hN
  apply heq_of_eq
  cases f; cases g
  cases eq_of_heq h
  rfl

theorem reductFunctor_id (S : FOL.Signature) : reductFunctor (𝟙 S) = 𝟭 (Model S) := by
  apply Functor.hext reduct_id
  intro M N f
  exact model_hom_hext (reduct_id M) (reduct_id N) _ _ HEq.rfl

theorem reductFunctor_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact model_hom_hext (reduct_comp f g M) (reduct_comp f g N) _ _ HEq.rfl

theorem decodeFunctor_naturality {S T : FOL.Signature} (f : S ⟶ T) :
    reductFunctor f ⋙ decodeFunctor S = decodeFunctor T ⋙ FOL.Structure.reduct f := rfl

/-- The target contains all native first-order matching sentences over the
marked signature, not merely the FOL translation image. -/
def institution : FOL.Signature ⥤ Room where
  obj S := ⟨FirstOrder.Sentence (signature S).symbols, Cat.of (Model S), fun M p => FirstOrder.Sentence.Satisfies M.base p⟩
  map f := ⟨SortMaps.Hom.sentence (signatureMap f), reductFunctor f,
    fun M p => SortMaps.Hom.satisfaction (signatureMap f) M.base p⟩
  map_id S := by
    apply Room.hom_ext
    · funext p
      change SortMaps.Hom.sentence (signatureMap (𝟙 S)) p = p
      rw [signatureMap_id, SortMaps.Hom.sentence_id]
    · exact reductFunctor_id S
  map_comp f g := by
    apply Room.hom_ext
    · funext p
      change SortMaps.Hom.sentence (signatureMap (f ≫ g)) p =
        SortMaps.Hom.sentence (signatureMap g) (SortMaps.Hom.sentence (signatureMap f) p)
      rw [signatureMap_comp, SortMaps.Hom.sentence_comp]
    · exact reductFunctor_comp f g
end Silmaril.Logic.Matching.GuardedFOL
