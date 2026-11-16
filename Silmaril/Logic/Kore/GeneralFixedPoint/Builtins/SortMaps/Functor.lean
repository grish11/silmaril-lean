module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Models

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Hom
open CategoryTheory

/-- Both carrier equivalences survive identity reduction as the same data. -/
theorem reduct_id (A : Signature)
    (M : @Model A.bindings A.scope A.literalPrefix A.literals A.hooks) :
    reduct (𝟙 A) M = M := by
  rcases A with ⟨⟨ai, ab, ad⟩, scope, literalPrefix, literals, hooks⟩
  rcases M with ⟨native, ⟨integer, boolean⟩, laws⟩
  cases native
  rfl

/-- Eliminating endpoint name equalities leaves exactly the same integer and
Boolean Equiv fields on both sides; only the Laws proof fields are irrelevant. -/
theorem reduct_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C)
    (M : @Model C.bindings C.scope C.literalPrefix C.literals C.hooks) :
    reduct (f ≫ g) M = reduct f (reduct g M) := by
  rcases A with ⟨⟨ai, ab, ad⟩, scopeA, prefixA, literalsA, hooksA⟩
  rcases B with ⟨⟨bi, bb, bd⟩, scopeB, prefixB, literalsB, hooksB⟩
  rcases C with ⟨⟨ci, cb, cd⟩, scopeC, prefixC, literalsC, hooksC⟩
  rcases f with ⟨f, hi, hb, labelsF⟩
  rcases g with ⟨g, gi, gb, labelsG⟩
  change ((⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeC.signature⟩ : Matching.SortMaps.Signature)) at g
  change ((⟨String, scopeA.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature)) at f
  change f.sorts ai = bi at hi
  change f.sorts ab = bb at hb
  subst bi
  subst bb
  change g.sorts (f.sorts ai) = ci at gi
  change g.sorts (f.sorts ab) = cb at gb
  subst ci
  subst cb
  rfl

/-- Every original native homomorphism is retained. -/
def reductMap {A B : Signature} (f : A ⟶ B)
    {M N : @Model B.bindings B.scope B.literalPrefix B.literals B.hooks}
    (h : M ⟶ N) : reduct f M ⟶ reduct f N := by
  change (@Model.native A.bindings A.scope A.literalPrefix A.literals A.hooks (reduct f M)) ⟶
    (@Model.native A.bindings A.scope A.literalPrefix A.literals A.hooks (reduct f N))
  rw [reduct_native, reduct_native]
  exact (Matching.SortMaps.Hom.reductFunctor f.native).map h

theorem reductMap_id {A B : Signature} (f : A ⟶ B)
    (M : @Model B.bindings B.scope B.literalPrefix B.literals B.hooks) :
    reductMap f (𝟙 M) = 𝟙 (reduct f M) := by
  rcases A with ⟨⟨ai, ab, ad⟩, scopeA, prefixA, literalsA, hooksA⟩
  rcases B with ⟨⟨bi, bb, bd⟩, scopeB, prefixB, literalsB, hooksB⟩
  rcases f with ⟨f, hi, hb, labels⟩
  change ((⟨String, scopeA.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature)) at f
  change f.sorts ai = bi at hi
  change f.sorts ab = bb at hb
  subst bi
  subst bb
  rfl

theorem reductMap_comp {A B : Signature} (f : A ⟶ B)
    {M N P : @Model B.bindings B.scope B.literalPrefix B.literals B.hooks}
    (h : M ⟶ N) (k : N ⟶ P) :
    reductMap f (h ≫ k) = reductMap f h ≫ reductMap f k := by
  rcases A with ⟨⟨ai, ab, ad⟩, scopeA, prefixA, literalsA, hooksA⟩
  rcases B with ⟨⟨bi, bb, bd⟩, scopeB, prefixB, literalsB, hooksB⟩
  rcases f with ⟨f, hi, hb, labels⟩
  change ((⟨String, scopeA.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature)) at f
  change f.sorts ai = bi at hi
  change f.sorts ab = bb at hb
  subst bi
  subst bb
  rfl

def reductFunctor {A B : Signature} (f : A ⟶ B) :
    @Model B.bindings B.scope B.literalPrefix B.literals B.hooks ⥤
      @Model A.bindings A.scope A.literalPrefix A.literals A.hooks where
  obj := reduct f
  map := reductMap f
  map_id := reductMap_id f
  map_comp := reductMap_comp f

private theorem native_hom_heq {A : Signature}
    {M M' N N' : @Model A.bindings A.scope A.literalPrefix A.literals A.hooks}
    (hM : M = M') (hN : N = N') (h : M ⟶ N) (k : M' ⟶ N')
    (same : HEq h.map k.map) : HEq h k := by
  cases hM
  cases hN
  exact heq_of_eq (Matching.FirstOrder.Model.Hom.ext _ _ (eq_of_heq same))

theorem reductFunctor_id (A : Signature) : reductFunctor (𝟙 A) = 𝟭 _ := by
  apply Functor.hext (reduct_id A)
  intro M N h
  apply native_hom_heq (reduct_id A M) (reduct_id A N)
  rcases A with ⟨⟨ai, ab, ad⟩, scope, literalPrefix, literals, hooks⟩
  rfl

theorem reductFunctor_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Functor.hext (reduct_comp f g)
  intro M N h
  apply native_hom_heq (reduct_comp f g M) (reduct_comp f g N)
  rcases A with ⟨⟨ai, ab, ad⟩, scopeA, prefixA, literalsA, hooksA⟩
  rcases B with ⟨⟨bi, bb, bd⟩, scopeB, prefixB, literalsB, hooksB⟩
  rcases C with ⟨⟨ci, cb, cd⟩, scopeC, prefixC, literalsC, hooksC⟩
  rcases f with ⟨f, hi, hb, labelsF⟩
  rcases g with ⟨g, gi, gb, labelsG⟩
  change ((⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeC.signature⟩ : Matching.SortMaps.Signature)) at g
  change ((⟨String, scopeA.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature)) at f
  change f.sorts ai = bi at hi
  change f.sorts ab = bb at hb
  subst bi
  subst bb
  change g.sorts (f.sorts ai) = ci at gi
  change g.sorts (f.sorts ab) = cb at gb
  subst ci
  subst cb
  rfl

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Hom
