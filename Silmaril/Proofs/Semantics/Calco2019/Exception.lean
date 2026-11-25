module

public import Silmaril.Semantics.Calco2019.Exception

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory Exception

variable {C : Type u} [Category.{v} C] (P : Coproducts C) (T : CategoryTheory.Monad C)

theorem exception_unit_extend {E X Y : C} (f : X ⟶ T.obj (P.sum Y E)) :
    unit P T E X ≫ extend P T f = f := by
  change (P.inl ≫ (KleisliTriple.ofMonad T).unit (P.sum X E)) ≫
    (KleisliTriple.ofMonad T).extend (P.desc f (raise P T E Y)) = f
  rw [Category.assoc, KleisliTriple.unit_extend]
  exact P.inl_desc f _

theorem exception_extend_unit (E X : C) :
    extend P T (unit P T E X) = 𝟙 (T.obj (P.sum X E)) := by
  change (KleisliTriple.ofMonad T).extend (P.desc (P.inl ≫ T.η.app _) (P.inr ≫ T.η.app _)) = _
  rw [← P.desc_comp, P.desc_inl_inr, Category.id_comp]
  exact (KleisliTriple.ofMonad T).extend_unit (P.sum X E)

theorem exception_extend_comp {E X Y Z : C}
    (f : X ⟶ T.obj (P.sum Y E)) (g : Y ⟶ T.obj (P.sum Z E)) :
    extend P T f ≫ extend P T g = extend P T (f ≫ extend P T g) := by
  let A := KleisliTriple.ofMonad T
  change A.extend (P.desc f (raise P T E Y)) ≫ A.extend (P.desc g (raise P T E Z)) =
    A.extend (P.desc (f ≫ A.extend (P.desc g (raise P T E Z))) (raise P T E Z))
  have e : raise P T E Y ≫ A.extend (P.desc g (raise P T E Z)) = raise P T E Z := by
    change (P.inr ≫ A.unit (P.sum Y E)) ≫ A.extend (P.desc g (raise P T E Z)) = _
    rw [Category.assoc, A.unit_extend]
    exact P.inr_desc g _
  let k := A.extend (P.desc g (raise P T E Z))
  exact (A.extend_comp (P.desc f (raise P T E Y)) (P.desc g (raise P T E Z))).trans
    (congrArg A.extend ((P.desc_comp f (raise P T E Y) k).trans (congrArg (P.desc (f ≫ k)) e)))

theorem exception_map {E X Y : C} (f : X ⟶ Y) :
    extend P T (f ≫ unit P T E Y) = T.map (P.map f (𝟙 E)) := by
  have e : P.desc (f ≫ unit P T E Y) (raise P T E Y) =
      P.map f (𝟙 E) ≫ T.η.app (P.sum Y E) := by
    simp [unit, raise, Coproducts.map]
  change T.map (P.desc (f ≫ unit P T E Y) (raise P T E Y)) ≫ T.μ.app (P.sum Y E) = _
  rw [e, Functor.map_comp, Category.assoc, T.right_unit, Category.comp_id]

theorem changeException_unit {E F : C} (h : E ⟶ F) (X : C) :
    unit P T E X ≫ changeException P T h X = unit P T F X := by
  simp [unit, changeException, ← T.η.naturality, Coproducts.map]

theorem changeException_extend {E F X Y : C} (h : E ⟶ F) (f : X ⟶ T.obj (P.sum Y E)) :
    extend P T f ≫ changeException P T h Y =
      changeException P T h X ≫ extend P T (f ≫ changeException P T h Y) := by
  let A := KleisliTriple.ofMonad T
  let i := P.map (𝟙 X) h
  let j := P.map (𝟙 Y) h
  let l := P.desc f (raise P T E Y)
  let r := P.desc (f ≫ T.map j) (raise P T F Y)
  have copair : l ≫ T.map j = i ≫ r := by
    simp [l, r, i, j, raise, Coproducts.map, ← T.η.naturality, Category.assoc]
  calc
    _ = A.extend (l ≫ T.map j) := by
      change (T.map l ≫ T.μ.app (P.sum Y E)) ≫ T.map j =
        T.map (l ≫ T.map j) ≫ T.μ.app (P.sum Y F)
      rw [Functor.map_comp, Category.assoc]
      exact (congrArg (fun w => T.map l ≫ w) (T.μ.naturality j).symm).trans
        (Category.assoc _ _ _).symm
    _ = A.extend (i ≫ r) := congrArg A.extend copair
    _ = _ := by
      change T.map (i ≫ r) ≫ T.μ.app (P.sum Y F) =
        T.map i ≫ T.map r ≫ T.μ.app (P.sum Y F)
      simp

theorem changeException_id (E X : C) : changeException P T (𝟙 E) X = 𝟙 _ := by
  simp [changeException, Coproducts.map]

theorem changeException_comp {E F G : C} (h : E ⟶ F) (k : F ⟶ G) (X : C) :
    changeException P T (h ≫ k) X = changeException P T h X ≫ changeException P T k X := by
  simp [changeException, ← Functor.map_comp, Coproducts.map]

end Silmaril.Calco2019.Proofs
