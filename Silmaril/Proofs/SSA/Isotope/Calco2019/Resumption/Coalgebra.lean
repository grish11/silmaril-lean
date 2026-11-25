module

public import Silmaril.SSA.Isotope.Calco2019.Resumption.Defs

public section

universe u v

namespace Silmaril.Isotope.Calco2019.Resumption.Proofs

open CategoryTheory Silmaril.Calco2019

section Guarded

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)
  {S Y : C} (coalgebra : S ⟶ (M.toParametrizedMonad.obj S).obj Y)

local notation "U" => M.toParametrizedMonad

private def resume : S ⟶ R.obj (P.sum Y S) :=
  P.inr ≫ R.unit (P.sum Y S)

private def prepared : S ⟶ ((U).obj (R.obj (P.sum Y S))).obj Y :=
  coalgebra ≫ ((U).parameter Y).map (resume M R)

private theorem first_observation :
    let T := (M.obj (R.obj (P.sum Y S))).monad
    kleisliArrow (T := T) (loopBody P R coalgebra ≫ R.out (P.sum Y S)) =
      kleisliArrow (T := T) (prepared M R coalgebra) ≫ (P.kleisli T).inl := by
  intro T
  apply Kleisli.hom_ext
  change (coalgebra ≫ ((U).parameter Y).map (resume M R) ≫
      T.map P.inl ≫ R.roll (P.sum Y S)) ≫ R.out (P.sum Y S) =
    prepared M R coalgebra ≫ T.map (P.inl ≫ T.η.app (P.sum Y S)) ≫ T.μ.app (P.sum Y S)
  have rollOut : R.roll (P.sum Y S) ≫ R.out (P.sum Y S) = 𝟙 (T.obj (P.sum Y S)) := R.roll_out _
  simp only [Category.assoc, rollOut, Category.comp_id, Functor.map_comp, T.right_unit]
  exact (Category.assoc _ _ _).symm

theorem loopBody_guarded :
    M.ResumptionGuard R (Y := Y) (Z := S) (loopBody P R coalgebra) := by
  let T := (M.obj (R.obj (P.sum Y S))).monad
  let Q := P.kleisli T
  have h := first_observation M R coalgebra
  exact Eq.mpr (congrArg (fun f : Kleisli.mk T S ⟶ Q.sum (.mk T Y) (.mk T S) =>
    (M.obj (R.obj (P.sum Y S))).guard.guarded (Y := .mk T Y) (Z := .mk T S) f) h)
    ((M.obj _).guard.trivial (kleisliArrow (prepared M R coalgebra)))

theorem iterate_eq_unfold
    (guard : M.ResumptionGuard R (Y := Y) (Z := S) (loopBody P R coalgebra)) :
    M.iterateResumption R (loopBody P R coalgebra) guard = R.unfold coalgebra := by
  let g := M.iterateResumption R (loopBody P R coalgebra) guard
  let d := M.diamond R (loopBody P R coalgebra) guard
  let T := (M.obj (R.obj (P.sum Y S))).monad
  let Q := P.kleisli T
  have fixed := (M.obj (R.obj (P.sum Y S))).iteration.fixpoint
    (kleisliArrow (T := T) (loopBody P R coalgebra ≫ R.out (P.sum Y S))) guard
  change kleisliArrow (T := T) (loopBody P R coalgebra ≫ R.out (P.sum Y S)) ≫
      Q.desc (𝟙 (Kleisli.mk T Y)) (kleisliArrow d) = kleisliArrow d at fixed
  rw [first_observation M R coalgebra] at fixed
  change (kleisliArrow (prepared M R coalgebra) ≫ Q.inl) ≫
      Q.desc (𝟙 (Kleisli.mk T Y)) (kleisliArrow d) = kleisliArrow d at fixed
  rw [Category.assoc, Q.inl_desc] at fixed
  have hd : d = prepared M R coalgebra :=
    congrArg Kleisli.Hom.of (fixed.symm.trans (Category.comp_id _))
  have sol : g ≫ R.out Y = d ≫ ((U).parameter Y).map (R.extend P (P.desc (R.unit Y) g)) :=
    (M.iterateResumption_characterization R (loopBody P R coalgebra) guard).1
  have next : resume (Y := Y) (S := S) M R ≫ R.extend P (P.desc (R.unit Y) g) = g := by
    rw [resume, Category.assoc, R.unit_extend, P.inr_desc]
  apply R.unfold_unique
  change g ≫ R.out Y = coalgebra ≫ ((U).parameter Y).map g
  rw [sol, hd, prepared, Category.assoc, ← Functor.map_comp, next]

end Guarded

section Observations

variable {M : ParametrizedMonad (Type u)} (B : Suspensions M) (D : ReadHeads B)
  (R : FinalResumptions M)

private theorem suspend_map {W V Y : Type u} (f : W ⟶ V) (next : Option W) :
    (M.parameter Y).map f (suspend B next) = suspend B (next.map f) := by
  have hm := congrFun (congrArg (fun g : (M.obj W).obj PEmpty ⟶ (M.obj V).obj Y => ⇑g)
    ((M.map f).naturality (↾(PEmpty.elim : PEmpty → Y)))) (B.app W next)
  have hb := congrFun (congrArg (fun g : Option W ⟶ (M.obj V).obj PEmpty => ⇑g)
    (B.naturality f)) next
  change B.app V (next.map f) = (M.map f).app PEmpty (B.app W next) at hb
  change (M.map f).app Y ((M.obj W).map (↾(PEmpty.elim : PEmpty → Y)) (B.app W next)) =
    (M.obj V).map (↾(PEmpty.elim : PEmpty → Y)) ((M.map f).app PEmpty (B.app W next)) at hm
  exact hm.trans (congrArg (fun a => (M.obj V).map (↾(PEmpty.elim : PEmpty → Y)) a) hb.symm)

theorem read_unfold {S Y : Type u} (step : S → Option (Y ⊕ S)) (s : S) :
    D.read (R.out Y (R.unfold (body B step) s)) =
      (step s).map (Sum.map id (R.unfold (body B step))) := by
  have h := congrFun (congrArg (fun f : S ⟶ (M.obj (R.obj Y)).obj Y => ⇑f)
    (R.unfold_spec (body B step))) s
  change R.out Y (R.unfold (body B step) s) =
    (M.parameter Y).map (R.unfold (body B step)) (body B step s) at h
  rw [h]
  change D.read ((M.parameter Y).map (R.unfold (body B step)) (match step s with
    | none => suspend B none
    | some (.inl y) => (M.obj S).η.app Y y
    | some (.inr t) => suspend B (some t))) = _
  cases step s with
  | none => rw [suspend_map, D.read_suspend]; rfl
  | some o =>
    cases o with
    | inr t => rw [suspend_map, D.read_suspend]; rfl
    | inl y =>
      have hy := congrFun (congrArg (fun f : Y ⟶ (M.obj (R.obj Y)).obj Y => ⇑f)
        ((M.map (R.unfold (body B step))).app_η Y)) y
      change (M.parameter Y).map (R.unfold (body B step)) ((M.obj S).η.app Y y) = _ at hy
      rw [hy, D.read_return]
      rfl

theorem finite_return_unfold {S Y : Type u} (step : S → Option (Y ⊕ S)) (s : S) (y : Y) :
    FiniteReturn (fun r => D.read (R.out Y r)) (R.unfold (body B step) s) y ↔
      FiniteReturn step s y := by
  constructor
  · intro h
    generalize e : R.unfold (body B step) s = r at h
    induction h generalizing s with
    | done h =>
      rw [← e, read_unfold B D R] at h
      cases hs : step s with
      | none => simp [hs] at h
      | some o =>
        cases o with
        | inl y' =>
          simp [hs] at h
          exact .done (by rw [hs, h])
        | inr => simp [hs] at h
    | next h _ ih =>
      rw [← e, read_unfold B D R] at h
      cases hs : step s with
      | none => simp [hs] at h
      | some o =>
        cases o with
        | inl => simp [hs] at h
        | inr t =>
          simp [hs] at h
          exact .next hs (ih t h)
  · intro h
    induction h with
    | done h => exact .done (by rw [read_unfold B D R, h]; rfl)
    | next h _ ih => exact .next (by rw [read_unfold B D R, h]; rfl) ih

end Observations

end Silmaril.Isotope.Calco2019.Resumption.Proofs
