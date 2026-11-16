module

public import Silmaril.Logic.Matching.GuardedLFP.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open CategoryTheory Silmaril.Logic.Institution.Examples

def sortMap {S T : FOL.Signature} (f : S ⟶ T) : MatchingSort S → MatchingSort T
  | .base s => .base (GuardedFOL.sortMap f s)
  | .tuple p => .tuple (p.map f)

def signatureMap {S T : FOL.Signature} (f : S ⟶ T) : signature S ⟶ signature T where
  sorts := sortMap f
  operations op := match op with
    | .base o => .base ((GuardedFOL.signatureMap f).operations o)
    | .pack p => .pack (p.map f)
    | .project p i => .project (p.map f) i
    | .active p => .active (p.map f)
    | .defined p => .defined (p.map f)
    | .liftTruth p => .liftTruth (p.map f)

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
    cases s with
    | base s => cases s <;> rfl
    | tuple p => rfl
  · intro n inputs output op
    cases op with
    | base o => cases o <;> rfl
    | pack p => rfl
    | project p i => rfl
    | active p => rfl
    | defined p => rfl
    | liftTruth p => rfl

theorem signatureMap_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    signatureMap (f ≫ g) = signatureMap f ≫ signatureMap g := by
  apply signature_hom_ext
  · funext s
    cases s with
    | base s => cases s <;> rfl
    | tuple p => rfl
  · intro n inputs output op
    cases op with
    | base o => cases o <;> rfl
    | pack p => rfl
    | project p i => rfl
    | active p => rfl
    | defined p => rfl
    | liftTruth p => rfl

def signatures : FOL.Signature ⥤ SortMaps.Signature where
  obj := signature
  map := signatureMap
  map_id := signatureMap_id
  map_comp := signatureMap_comp

/-- Equality-only arrows match the source LFP model category. -/
instance (S : FOL.Signature) : Category (Model S) where
  Hom M N := PLift (M = N)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

def decodeFunctor (S : FOL.Signature) : Model S ⥤ FirstOrderLFP.Model S where
  obj := decode
  map h := ⟨congrArg decode h.down⟩

@[ext] theorem Model.ext {S : FOL.Signature} (M N : Model S) (h : M.base = N.base) : M = N := by
  cases M; cases N; cases h; rfl

def reduct {S T : FOL.Signature} (f : S ⟶ T) (M : Model T) : Model S where
  base := SortMaps.Hom.reduct (signatureMap f) M.base
  function op args := M.function (f.ops op) args
  relation r args := M.relation (f.rels r) args
  objectDefined s args := M.objectDefined (f.sorts s) args
  truth args := M.truth args
  pack_total p args := M.pack_total (p.map f) args
  pack_strict p args y h := M.pack_strict (p.map f) args y h
  project_total p y i := M.project_total (p.map f) y i
  project_pack p args y h := M.project_pack (p.map f) args y h
  tuple_ext p x y h := M.tuple_ext (p.map f) x y h
  tupleDefined p args := M.tupleDefined (p.map f) args
  truthLift p args := M.truthLift (p.map f) args

theorem decode_reduct {S T : FOL.Signature} (f : S ⟶ T) (M : Model T) :
    decode (reduct f M) = (FirstOrderLFP.reduct f).obj (decode M) := rfl

def reductFunctor {S T : FOL.Signature} (f : S ⟶ T) : Model T ⥤ Model S where
  obj := reduct f
  map h := ⟨congrArg (reduct f) h.down⟩

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

private theorem equality_hom_heq {S : FOL.Signature} {M M' N N' : Model S}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N') : HEq f g := by
  cases hM
  cases hN
  apply heq_of_eq
  cases f
  cases g
  rfl

theorem reductFunctor_id (S : FOL.Signature) : reductFunctor (𝟙 S) = 𝟭 (Model S) := by
  apply Functor.hext reduct_id
  intro M N f
  exact equality_hom_heq (reduct_id M) (reduct_id N) _ _

theorem reductFunctor_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  exact equality_hom_heq (reduct_comp f g M) (reduct_comp f g N) _ _

theorem decodeFunctor_naturality {S T : FOL.Signature} (f : S ⟶ T) :
    reductFunctor f ⋙ decodeFunctor S = decodeFunctor T ⋙ FirstOrderLFP.reduct f := rfl
end Silmaril.Logic.Matching.GuardedLFP
