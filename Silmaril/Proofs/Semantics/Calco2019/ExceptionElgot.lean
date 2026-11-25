module

public import Silmaril.Semantics.Calco2019.ExceptionUniformity
import Silmaril.Proofs.Semantics.Calco2019.ResumptionCodiagonal
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard
import Silmaril.Semantics.Calco2019.Thms

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory Exception

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P) (E : C)

private theorem exception_comp_of {X Y Z : Kleisli ((family P T.monad).obj E)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).of = f.of ≫ extend P T.monad (E := E) g.of :=
  congrArg (fun z => f.of ≫ z) (family_extend P T.monad E g.of)

private theorem normalized_naturality_body {X Y Z : Kleisli ((family P T.monad).obj E)}
    (f : X ⟶ (P.kleisli ((family P T.monad).obj E)).sum Y X) (g : Y ⟶ Z) :
    kleisliArrow ((f ≫ (P.kleisli ((family P T.monad).obj E)).map g (𝟙 X)).of ≫
      T.monad.map (rearrange P E (Y := Z.of) (Z := X.of))) =
    kleisliArrow (f.of ≫ T.monad.map (rearrange P E (Y := Y.of) (Z := X.of))) ≫
      (P.kleisli T.monad).map
        (kleisliArrow (P.desc g.of (raise P T.monad E Z.of)))
        (𝟙 (Kleisli.mk T.monad X.of)) := by
  let L := (family P T.monad).obj E
  let Q := T.monad
  let K := P.kleisli Q
  let jY := rearrange P E (Y := Y.of) (Z := X.of)
  let jZ := rearrange P E (Y := Z.of) (Z := X.of)
  let k := (P.kleisli L).map g (𝟙 X)
  let g' : Kleisli.mk Q (P.sum Y.of E) ⟶ Kleisli.mk Q (P.sum Z.of E) :=
    kleisliArrow (P.desc g.of (raise P Q E Z.of))
  let k' := K.map g' (𝟙 (Kleisli.mk Q X.of))
  have hg : (g ≫ (P.kleisli L).inl (Y := X)).of =
      g.of ≫ Q.map (P.map (P.inl (X := Z.of) (Y := X.of)) (𝟙 E)) :=
    (comp_pure_of L g _).trans (congrArg (fun w => g.of ≫ w) (family_map P Q E _))
  have hk : k.of = P.desc (g ≫ (P.kleisli L).inl (Y := X)).of ((P.kleisli L).inr (X := Z) (Y := X)).of := by
    exact (kleisli_desc_of P L _ _).trans (by rw [Category.id_comp])
  have hkl : ((P.kleisli L).inr (X := Z) (Y := X)).of =
      P.inr ≫ P.inl ≫ Q.η.app (P.sum (P.sum Z.of X.of) E) := rfl
  have hk' : k'.of = P.desc (g'.of ≫ Q.map P.inl)
        (P.inr ≫ Q.η.app (P.sum (P.sum Z.of E) X.of)) := by
    change (K.desc (g' ≫ K.inl) ((𝟙 _) ≫ K.inr)).of = _
    rw [Category.id_comp, kleisli_desc_of]
    exact congrArg (fun a => P.desc a (P.inr ≫ Q.η.app (P.sum (P.sum Z.of E) X.of)))
      (comp_pure_of Q g' P.inl)
  have h : P.desc k.of (raise P Q E (P.sum Z.of X.of)) ≫ Q.map jZ = jY ≫ k'.of := by
    rw [hk, hg, hkl, hk']
    have hj : P.map (P.inl (X := Z.of) (Y := X.of)) (𝟙 E) ≫ jZ =
        P.inl (X := P.sum Z.of E) (Y := X.of) := by
      apply P.hom_ext <;> simp [jZ, rearrange, Coproducts.map]
    apply P.hom_ext
    · simp only [jY, rearrange, Coproducts.inl_desc_assoc]
      apply P.hom_ext
      · simp [g', Category.assoc, ← Functor.map_comp, hj]
      · simp [jZ, Category.assoc, ← Q.η.naturality, rearrange]
    · simp [g', jY, jZ, raise, Category.assoc, ← Q.η.naturality, rearrange]
  apply Kleisli.hom_ext
  change (f ≫ k).of ≫ Q.map jZ = (f.of ≫ Q.map jY) ≫ Q.map k'.of ≫ Q.μ.app _
  calc
    (f ≫ k).of ≫ Q.map jZ =
        (f.of ≫ Q.map (P.desc k.of (raise P Q E (P.sum Z.of X.of))) ≫ Q.μ.app (P.sum (P.sum Z.of X.of) E)) ≫ Q.map jZ :=
      congrArg (· ≫ Q.map jZ) (exception_comp_of T E f k)
    _ = f.of ≫ Q.map (P.desc k.of (raise P Q E (P.sum Z.of X.of)) ≫ Q.map jZ) ≫ Q.μ.app _ := by
      have hm : Q.μ.app _ ≫ Q.map jZ = Q.map (Q.map jZ) ≫ Q.μ.app _ := (Q.μ.naturality jZ).symm
      simp only [Category.assoc, hm, ← Functor.map_comp_assoc]
    _ = f.of ≫ Q.map (jY ≫ k'.of) ≫ Q.μ.app _ :=
      congrArg (fun c => f.of ≫ Q.map c ≫ Q.μ.app _) h
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]

theorem exception_naturality (E : C) {X Y Z : Kleisli ((family P T.monad).obj E)}
    (f : X ⟶ (P.kleisli ((family P T.monad).obj E)).sum Y X) (g : Y ⟶ Z)
    (hf : (guardedness T E).guarded f)
    (hg : (guardedness T E).guarded (f ≫ (P.kleisli ((family P T.monad).obj E)).map g (𝟙 X))) :
    (fixpoints T E).iterate (f ≫ (P.kleisli ((family P T.monad).obj E)).map g (𝟙 X)) hg =
      (fixpoints T E).iterate f hf ≫ g := by
  let Q := T.monad
  let K := P.kleisli Q
  let a : Kleisli.mk Q X.of ⟶ Kleisli.mk Q (P.sum (P.sum Y.of E) X.of) :=
    kleisliArrow (f.of ≫ Q.map (rearrange P E))
  let g' : Kleisli.mk Q (P.sum Y.of E) ⟶ Kleisli.mk Q (P.sum Z.of E) :=
    kleisliArrow (P.desc g.of (raise P Q E Z.of))
  let b := a ≫ K.map g' (𝟙 (Kleisli.mk Q X.of))
  have ha : T.guard.guarded (Y := Kleisli.mk Q (P.sum Y.of E)) (Z := Kleisli.mk Q X.of) a := hf
  have hb : T.guard.guarded (Y := Kleisli.mk Q (P.sum Z.of E)) (Z := Kleisli.mk Q X.of) b :=
    Guardedness.map ha g' (𝟙 _)
  have h := iterate_congr T.iteration.toFixpoints (normalized_naturality_body T E f g) hg hb
  have n := T.iteration.naturalCodiagonal.naturality a g' ha hb
  apply Kleisli.hom_ext
  exact (congrArg Kleisli.Hom.of (h.trans n)).trans
    (exception_comp_of T E ((fixpoints T E).iterate f hf) g).symm

private theorem exception_comp_pure_of {X Y Z : C}
    (f : Kleisli.mk ((family P T.monad).obj E) X ⟶ Kleisli.mk ((family P T.monad).obj E) Y)
    (g : Y ⟶ Z) :
    (f ≫ (Kleisli.Adjunction.toKleisli ((family P T.monad).obj E)).map g).of =
      f.of ≫ T.monad.map (P.map g (𝟙 E)) :=
  (comp_pure_of _ f g).trans (congrArg (fun j => f.of ≫ j) (family_map P T.monad E g))

private theorem rearrange_assoc (Y X : C) :
    rearrange P E (Y := P.sum Y X) (Z := X) ≫
        P.map (rearrange P E (Y := Y) (Z := X)) (𝟙 X) ≫ P.assoc =
      P.map (P.assoc (X := Y) (Y := X) (Z := X)) (𝟙 E) ≫ rearrange P E := by
  apply P.hom_ext
  · apply P.hom_ext
    · apply P.hom_ext <;> simp [Coproducts.assoc, Coproducts.map, rearrange]
    · simp [Coproducts.assoc, Coproducts.map, rearrange]
  · simp [Coproducts.assoc, Coproducts.map, rearrange]

private theorem rearrange_merge (Y X : C) :
    rearrange P E (Y := P.sum Y X) (Z := X) ≫
        P.map (rearrange P E (Y := Y) (Z := X)) (𝟙 X) ≫ P.merge =
      P.map (P.merge (Y := Y) (X := X)) (𝟙 E) ≫ rearrange P E := by
  apply P.hom_ext
  · apply P.hom_ext
    · apply P.hom_ext <;> simp [Coproducts.merge, Coproducts.map, rearrange]
    · simp [Coproducts.merge, Coproducts.map, rearrange]
  · simp [Coproducts.merge, Coproducts.map, rearrange]

theorem exception_codiagonal (E : C) {X Y : Kleisli ((family P T.monad).obj E)}
    (f : X ⟶ (P.kleisli ((family P T.monad).obj E)).sum
      ((P.kleisli ((family P T.monad).obj E)).sum Y X) X)
    (hf : (guardedness T E).nested f) (hi : (guardedness T E).guarded f)
    (ho : (guardedness T E).guarded ((fixpoints T E).iterate f hi))
    (hm : (guardedness T E).guarded (f ≫ (P.kleisli ((family P T.monad).obj E)).merge)) :
    (fixpoints T E).iterate (f ≫ (P.kleisli ((family P T.monad).obj E)).merge) hm =
      (fixpoints T E).iterate ((fixpoints T E).iterate f hi) ho := by
  let Q := T.monad
  let L := (family P Q).obj E
  let K := P.kleisli Q
  let J := Kleisli.Adjunction.toKleisli Q
  let x := Kleisli.mk Q X.of
  let y := Kleisli.mk Q (P.sum Y.of E)
  let z := Kleisli.mk Q (P.sum (P.sum Y.of X.of) E)
  let j := rearrange P E (Y := Y.of) (Z := X.of)
  let i := rearrange P E (Y := P.sum Y.of X.of) (Z := X.of)
  let a : x ⟶ K.sum z x := kleisliArrow (f.of ≫ Q.map i)
  let b : x ⟶ K.sum (K.sum y x) x := a ≫ K.map (J.map j) (𝟙 x)
  have ha : T.guard.guarded (Y := z) (Z := x) a := hi
  have hb : T.guard.guarded (Y := K.sum y x) (Z := x) b := Guardedness.map ha _ _
  have be : b.of = f.of ≫ Q.map (i ≫ P.map j (𝟙 X.of)) := by
    change (a ≫ K.map (J.map j) (𝟙 x)).of = _
    have hid : 𝟙 x = J.map (𝟙 X.of) := (J.map_id X.of).symm
    rw [hid, kleisli_map_pure, comp_pure_of]
    change (f.of ≫ Q.map i) ≫ Q.map (P.map j (𝟙 X.of)) = _
    simp only [Functor.map_comp, Category.assoc]
  have assoc_eq :
      (b ≫ K.assoc).of = (f ≫ (P.kleisli L).assoc).of ≫
        Q.map (rearrange P E (Y := Y.of) (Z := P.sum X.of X.of)) := by
    rw [kleisli_assoc_pure Q (P.sum Y.of E) X.of X.of, comp_pure_of, be]
    rw [kleisli_assoc_pure L Y.of X.of X.of, exception_comp_pure_of]
    dsimp only [Q]
    simp only [Category.assoc, ← Functor.map_comp]
    exact congrArg (fun k => f.of ≫ Q.map k) (rearrange_assoc E Y.of X.of)
  have hnb : T.guard.nested (Y := y) (Z := x) (W := x) b := by
    change T.guard.guarded (Y := y) (Z := K.sum x x) (b ≫ K.assoc)
    rw [Kleisli.hom_ext assoc_eq]
    exact hf
  have merge_eq : b ≫ K.merge =
      kleisliArrow ((f ≫ (P.kleisli L).merge).of ≫ Q.map j) := by
    apply Kleisli.hom_ext
    rw [kleisli_merge_pure Q X.of (P.sum Y.of E), comp_pure_of, be]
    change _ = (f ≫ (P.kleisli L).merge).of ≫ Q.map j
    rw [kleisli_merge_pure L X.of Y.of, exception_comp_pure_of]
    dsimp only [Q]
    simp only [Category.assoc, ← Functor.map_comp]
    exact congrArg (fun k => f.of ≫ Q.map k) (rearrange_merge E Y.of X.of)
  have hm' : T.guard.guarded (Y := y) (Z := x) (b ≫ K.merge) := by
    rw [merge_eq]
    exact hm
  have outer_eq : T.iteration.iterate b hb =
      kleisliArrow (((fixpoints T E).iterate f hi).of ≫ Q.map j) := by
    apply Kleisli.hom_ext
    exact (congrArg Kleisli.Hom.of (T.iteration.naturalCodiagonal.naturality a (J.map j) ha hb)).trans
      (comp_pure_of Q (T.iteration.iterate a ha) j)
  have ho' : T.guard.guarded (Y := y) (Z := x) (T.iteration.iterate b hb) := by
    rw [outer_eq]
    exact ho
  let I := T.iteration.toFixpoints
  have left := iterate_congr I merge_eq hm' hm
  have right := iterate_congr I outer_eq ho' ho
  have eq := T.iteration.naturalCodiagonal.codiagonal b hnb hb ho' hm'
  have e := left.symm.trans (eq.trans right)
  exact Kleisli.hom_ext (congrArg (fun q : x ⟶ y => q.of) e)

end Silmaril.Calco2019.Proofs
