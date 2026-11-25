module

public import Silmaril.Semantics.Calco2019.ExceptionGuard
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard
import Silmaril.Semantics.Calco2019.Thms

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory Exception

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

section Guard

variable (T : CategoryTheory.Monad C) (E : C)

private theorem exception_comp_of {X Y Z : Kleisli ((family P T).obj E)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).of = f.of ≫ extend P T (E := E) g.of :=
  congrArg (fun z => f.of ≫ z) (family_extend P T E g.of)

variable (G : MonadGuardedness P T)

theorem exception_guard_trivial {X Y Z : Kleisli ((family P T).obj E)}
    (f : X ⟶ Y) : kleisliGuardOf P G E (f ≫ (P.kleisli ((family P T).obj E)).inl (Y := Z)) := by
  let L := (family P T).obj E
  let j : Y.of ⟶ P.sum Y.of Z.of := P.inl
  let s := rearrange P E (Y := Y.of) (Z := Z.of)
  have rearr : P.map j (𝟙 E) ≫ s = P.inl := by
    apply P.hom_ext <;> simp [j, s, rearrange, Coproducts.map]
  have e : (f ≫ (P.kleisli L).inl (Y := Z)).of ≫ T.map s =
      f.of ≫ T.map (P.inl (X := P.sum Y.of E) (Y := Z.of)) :=
    (congrArg (· ≫ T.map s) (comp_pure_of L f j)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun w => f.of ≫ w)
        ((congrArg (· ≫ T.map s) (family_map P T E j)).trans
          (((T.toFunctor).map_comp (P.map j (𝟙 E)) s).symm.trans
            (congrArg T.map rearr)))))
  have guarded := G.trivial (Z := Kleisli.mk T Z.of) (kleisliArrow f.of)
  have bodyEq : (((kleisliArrow f.of : Kleisli.mk T X.of ⟶ Kleisli.mk T (P.sum Y.of E)) ≫
      (P.kleisli T).inl (Y := Kleisli.mk T Z.of))).of =
      (f ≫ (P.kleisli L).inl (Y := Z)).of ≫ T.map s :=
    (comp_pure_of T _ P.inl).trans e.symm
  exact Eq.mp (congrArg (G.guarded (Y := Kleisli.mk T (P.sum Y.of E)) (Z := Kleisli.mk T Z.of))
    (Kleisli.hom_ext bodyEq)) guarded

theorem exception_guard_parallel {X X' Y Z : Kleisli ((family P T).obj E)}
    {f : X ⟶ (P.kleisli ((family P T).obj E)).sum Y Z}
    {g : X' ⟶ (P.kleisli ((family P T).obj E)).sum Y Z}
    (hf : kleisliGuardOf P G E (Y := Y) (Z := Z) f) (hg : kleisliGuardOf P G E (Y := Y) (Z := Z) g) :
    kleisliGuardOf P G E (Y := Y) (Z := Z) ((P.kleisli ((family P T).obj E)).desc f g) := by
  let s := T.map (rearrange P E (Y := Y.of) (Z := Z.of))
  let K := P.kleisli T
  let f' : Kleisli.mk T X.of ⟶ Kleisli.mk T (P.sum (P.sum Y.of E) Z.of) :=
    kleisliArrow (f.of ≫ s)
  let g' : Kleisli.mk T X'.of ⟶ Kleisli.mk T (P.sum (P.sum Y.of E) Z.of) :=
    kleisliArrow (g.of ≫ s)
  have e : ((P.kleisli ((family P T).obj E)).desc f g).of ≫ s = (K.desc f' g').of :=
    (congrArg (· ≫ s) (kleisli_desc_of P _ f g)).trans
      ((P.desc_comp f.of g.of s).trans (kleisli_desc_of P T f' g').symm)
  exact Eq.mpr (congrArg (G.guarded (Y := Kleisli.mk T (P.sum Y.of E))
    (Z := Kleisli.mk T Z.of)) (Kleisli.hom_ext e)) (G.parallel hf hg)

theorem exception_guard_compose {X Y Z V W : Kleisli ((family P T).obj E)}
    {f : X ⟶ (P.kleisli ((family P T).obj E)).sum Y Z}
    {g : Y ⟶ (P.kleisli ((family P T).obj E)).sum V W}
    (h : Z ⟶ (P.kleisli ((family P T).obj E)).sum V W)
    (hf : kleisliGuardOf P G E (Y := Y) (Z := Z) f) (hg : kleisliGuardOf P G E (Y := V) (Z := W) g) :
    kleisliGuardOf P G E (Y := V) (Z := W) (f ≫ (P.kleisli ((family P T).obj E)).desc g h) := by
  let L := (family P T).obj E
  let A := P.sum V.of W.of
  let B := P.sum (P.sum V.of E) W.of
  let s : P.sum (P.sum Y.of Z.of) E ⟶ P.sum (P.sum Y.of E) Z.of := rearrange P E
  let t : P.sum A E ⟶ B := rearrange P E
  let k := (P.kleisli L).desc g h
  let T' := T
  let K := P.kleisli T'
  let a : Kleisli.mk T' X.of ⟶ Kleisli.mk T' (P.sum (P.sum Y.of E) Z.of) :=
    kleisliArrow (f.of ≫ T'.map s)
  let left : Kleisli.mk T' Y.of ⟶ Kleisli.mk T' B := kleisliArrow (g.of ≫ T'.map t)
  let right : Kleisli.mk T' Z.of ⟶ Kleisli.mk T' B := kleisliArrow (h.of ≫ T'.map t)
  let err : Kleisli.mk T' E ⟶ Kleisli.mk T' B := kleisliArrow (raise P T' E A ≫ T'.map t)
  have errEq : err.of = raise P T' E V.of ≫ T'.map (P.inl (X := P.sum V.of E) (Y := W.of)) := by
    simp [err, t, A, B, T', raise, rearrange, Category.assoc, ← T.η.naturality]
  have herr : G.guarded (Y := Kleisli.mk T' (P.sum V.of E)) (Z := Kleisli.mk T' W.of) err :=
    Eq.mpr (congrArg (G.guarded (Y := Kleisli.mk T' (P.sum V.of E)) (Z := Kleisli.mk T' W.of))
      (Kleisli.hom_ext (errEq.trans (comp_pure_of T' (kleisliArrow (raise P T' E V.of)) P.inl).symm)))
      (G.trivial (kleisliArrow (raise P T' E V.of)))
  have guarded := G.compose right hf (G.parallel hg herr)
  let F := P.sum (P.sum Y.of Z.of) E
  let f' : X.of ⟶ T'.obj F := f.of
  let g' : Y.of ⟶ T'.obj (P.sum A E) := g.of
  let h' : Z.of ⟶ T'.obj (P.sum A E) := h.of
  let c : F ⟶ T'.obj (P.sum A E) := P.desc (P.desc g' h') (raise P T' E A)
  let d : P.sum (P.sum Y.of E) Z.of ⟶ T'.obj B := P.desc (P.desc left.of err.of) right.of
  have ec : c ≫ T'.map t = s ≫ d := by
    simp [c, s, d, left, right, err, rearrange, g', h', Category.assoc]
    exact congrArg (fun z => P.desc z (raise P T' E A ≫ T'.map t)) (P.desc_comp g' h' (T'.map t))
  have kd : (K.desc (K.desc left err) right).of = d :=
    (kleisli_desc_of P T' _ _).trans (congrArg (fun w => P.desc w right.of) (kleisli_desc_of P T' _ _))
  have e : (f ≫ k).of ≫ T'.map t = (a ≫ K.desc (K.desc left err) right).of := by
    have el : k.of = P.desc g' h' := kleisli_desc_of P L _ _
    let c' : F ⟶ T'.obj (P.sum A E) := P.desc k.of (raise P T' E A)
    have cEq : c' = c := congrArg (fun z => P.desc z (raise P T' E A)) el
    have mu : T'.μ.app (P.sum A E) ≫ T'.map t = T'.map (T'.map t) ≫ T'.μ.app B :=
      (T'.μ.naturality t).symm
    calc
      _ = (f' ≫ (T'.map c' ≫ T'.μ.app (P.sum A E))) ≫ T'.map t :=
        congrArg (· ≫ T'.map t) (exception_comp_of T E f k)
      _ = f' ≫ T'.map (c ≫ T'.map t) ≫ T'.μ.app B := by
        simp only [cEq, Category.assoc, Functor.map_comp, mu]
      _ = f' ≫ T'.map (s ≫ d) ≫ T'.μ.app B :=
        congrArg (fun z => f' ≫ T'.map z ≫ T'.μ.app B) ec
      _ = _ := by
        change f' ≫ T'.map (s ≫ d) ≫ T'.μ.app B =
          (f' ≫ T'.map s) ≫ T'.map (K.desc (K.desc left err) right).of ≫ T'.μ.app B
        simp only [kd, Functor.map_comp, Category.assoc]
  exact Eq.mpr (congrArg (G.guarded (Y := Kleisli.mk T' (P.sum V.of E)) (Z := Kleisli.mk T' W.of))
    (Kleisli.hom_ext e)) guarded

private theorem change_normalized_arrow {E' X Y Z : C} (h : E ⟶ E')
    (f : X ⟶ T.obj (P.sum (P.sum Y Z) E)) :
    (f ≫ changeException P T h (P.sum Y Z)) ≫ T.map (rearrange P E' (Y := Y) (Z := Z)) =
      (f ≫ T.map (rearrange P E (Y := Y) (Z := Z))) ≫
        T.map (P.map (P.map (𝟙 Y) h) (𝟙 Z)) := by
  have e : P.map (𝟙 (P.sum Y Z)) h ≫ rearrange P E' =
      rearrange P E ≫ P.map (P.map (𝟙 Y) h) (𝟙 Z) := by
    simp [rearrange, Coproducts.map, Category.assoc]
  simp only [changeException, Category.assoc, ← Functor.map_comp]
  exact congrArg (fun j => f ≫ T.map j) e

private theorem normalized_pure_map {E' X Y Z : C} (h : E ⟶ E')
    (f : X ⟶ T.obj (P.sum (P.sum Y Z) E)) :
    kleisliArrow (f ≫ T.map (rearrange P E (Y := Y) (Z := Z))) ≫
      (P.kleisli T).map ((Kleisli.Adjunction.toKleisli T).map (P.map (𝟙 Y) h))
        (𝟙 (Kleisli.mk T Z)) =
      kleisliArrow ((f ≫ changeException P T h (P.sum Y Z)) ≫
        T.map (rearrange P E' (Y := Y) (Z := Z))) := by
  let J := Kleisli.Adjunction.toKleisli T
  have e : 𝟙 (Kleisli.mk T Z) = J.map (𝟙 Z) := (J.map_id Z).symm
  rw [e, kleisli_map_pure]
  exact Kleisli.hom_ext ((comp_pure_of T _ _).trans (change_normalized_arrow T E h f).symm)

theorem change_guard {E' X Y Z : C} (h : E ⟶ E')
    {f : X ⟶ T.obj (P.sum (P.sum Y Z) E)} (hf : guardOf P G E (Y := Y) (Z := Z) f) :
    guardOf P G E' (Y := Y) (Z := Z) (f ≫ changeException P T h (P.sum Y Z)) := by
  have hg := Guardedness.map hf ((Kleisli.Adjunction.toKleisli T).map (P.map (𝟙 Y) h))
    (𝟙 (Kleisli.mk T Z))
  exact Eq.mp (congrArg (G.guarded (Y := Kleisli.mk T (P.sum Y E'))
    (Z := Kleisli.mk T Z)) (normalized_pure_map T E h f)) hg

end Guard

section Iteration
variable (T : GuardedElgotMonad P) (E : C)

theorem exception_iteration_fixpoint {X Y : C} (f : X ⟶ T.monad.obj (P.sum (P.sum Y X) E))
    (hf : Guard P T E (Y := Y) (Z := X) f) :
    f ≫ extend P T.monad (P.desc (unit P T.monad E Y) (iterate P T E f hf)) =
      iterate P T E f hf := by
  let A := P.sum Y E
  let B := P.sum (P.sum Y X) E
  let Q := T.monad
  let K := P.kleisli Q
  let sh : B ⟶ P.sum A X := rearrange P E
  let a : Kleisli.mk Q X ⟶ Kleisli.mk Q (P.sum A X) := kleisliArrow (f ≫ Q.map sh)
  let q := T.iteration.iterate a hf
  have f' : (a ≫ K.desc (𝟙 (Kleisli.mk Q A)) q).of = q.of :=
    congrArg Kleisli.Hom.of (T.iteration.fixpoint a hf)
  have dEq : (K.desc (𝟙 (Kleisli.mk Q A)) q).of = P.desc (Q.η.app A) q.of :=
    kleisli_desc_of P Q _ _
  have h : sh ≫ P.desc (Q.η.app A) q.of =
      P.desc (P.desc (unit P Q E Y) q.of) (raise P Q E Y) := by
    simp [sh, A, rearrange, unit, raise]
  have body : (a ≫ K.desc (𝟙 (Kleisli.mk Q A)) q).of =
      f ≫ extend P Q (P.desc (unit P Q E Y) q.of) := by
    change (f ≫ Q.map sh) ≫ Q.map (K.desc (𝟙 (Kleisli.mk Q A)) q).of ≫ Q.μ.app A =
      f ≫ Q.map (P.desc (P.desc (unit P Q E Y) q.of) (raise P Q E Y)) ≫ Q.μ.app A
    rw [dEq, Category.assoc, ← Functor.map_comp_assoc, h]
  exact body.symm.trans f'

theorem exception_fixpoint {X Y : Kleisli ((family P T.monad).obj E)}
    (f : X ⟶ (P.kleisli ((family P T.monad).obj E)).sum Y X)
    (hf : kleisliGuard P T E (Y := Y) (Z := X) f) :
    Guardedness.IsFixpoint f (kleisliArrow (iterate P T E f.of hf)) := by
  let L := (family P T.monad).obj E
  let q : X ⟶ Y := kleisliArrow (iterate P T E f.of hf)
  change f ≫ (P.kleisli L).desc (𝟙 Y) q = q
  apply Kleisli.hom_ext
  exact (exception_comp_of T.monad E f _).trans
    ((congrArg (fun a => f.of ≫ extend P T.monad a) (kleisli_desc_of P L (𝟙 Y) q)).trans
      (exception_iteration_fixpoint T E f.of hf))

theorem change_iterate {E' X Y : C} (h : E ⟶ E')
    {f : X ⟶ T.monad.obj (P.sum (P.sum Y X) E)} (hf : Guard P T E (Y := Y) (Z := X) f) :
    iterate P T E f hf ≫ changeException P T.monad h Y =
      iterate P T E' (f ≫ changeException P T.monad h (P.sum Y X)) (change_guard T.monad E T.guard h hf) := by
  let Z := P.sum Y E
  let a : Kleisli.mk T.monad X ⟶ Kleisli.mk T.monad (P.sum Z X) :=
    kleisliArrow (f ≫ T.monad.map (rearrange P E))
  let j := (Kleisli.Adjunction.toKleisli T.monad).map (P.map (𝟙 Y) h)
  let b := a ≫ (P.kleisli T.monad).map j (𝟙 (Kleisli.mk T.monad X))
  have hb : T.guard.guarded (Y := Kleisli.mk T.monad (P.sum Y E'))
      (Z := Kleisli.mk T.monad X) b := Guardedness.map hf j (𝟙 _)
  have natural := T.iteration.naturalCodiagonal.naturality a j hf hb
  have e := iterate_congr T.iteration.toFixpoints (normalized_pure_map T.monad E h f) hb
    (change_guard T.monad E T.guard h hf)
  exact (comp_pure_of T.monad (T.iteration.iterate a hf) (P.map (𝟙 Y) h)).symm.trans
    (congrArg Kleisli.Hom.of (natural.symm.trans e))

end Iteration

end Silmaril.Calco2019.Proofs
