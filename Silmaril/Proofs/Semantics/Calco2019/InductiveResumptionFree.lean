module

public import Silmaril.Semantics.Calco2019.InductiveResumption.Free.Defs
public import Silmaril.Semantics.Calco2019.Vacuous
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs.InductiveResumptionFree

open CategoryTheory CategoryTheory.Limits Inductive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] (P : Coproducts C)
  {T S : CategoryTheory.Monad C} {H : C ⥤ C}
  (ξ : T ⟶ S) (σ : H ⟶ (S : C ⥤ C))

local notation "A" => KleisliTriple.ofMonad S
local notation "M" => Exception.parametrized P T H

private theorem parameter_map {X W W' : C} (k : W ⟶ W') :
    ((M).parameter X).map k = T.map (P.map (𝟙 X) (H.map k)) := rfl

private theorem fibre_extend {X Y W : C} (f : X ⟶ T.obj (P.sum Y (H.obj W))) :
    (M).extend (W := W) f = Exception.extend P T f :=
  Exception.family_extend P T (H.obj W) f

private theorem operation_extend {X Y : C} (k : X ⟶ S.obj Y) :
    runOperation σ X ≫ (A).extend k = H.map ((A).extend k) ≫ runOperation σ Y := by
  have e : S.μ.app X ≫ (A).extend k = (A).extend ((A).extend k) := by
    have hh := (A).extend_comp (𝟙 (S.obj X)) k
    simpa only [KleisliTriple.ofMonad, Functor.map_id, Category.id_comp] using hh
  simp only [runOperation, Category.assoc, e]
  have n := σ.naturality_assoc ((A).extend k) (S.μ.app Y)
  exact n.symm

private theorem algebra_extend {X Y : C} (f : X ⟶ S.obj Y) :
    interpretationAlgebra P ξ σ X ≫ (A).extend f =
      ((M).parameter X).map ((A).extend f) ≫ ξ.app _ ≫
        (A).extend (P.desc f (runOperation σ Y)) := by
  let b := (A).extend f
  let k := P.map (𝟙 X) (H.map b)
  let c := P.desc f (runOperation σ Y)
  have bc : (P.desc (S.η.app X) (runOperation σ X)) ≫ b = k ≫ c := by
    have e : S.η.app X ≫ b = f := (A).unit_extend f
    rw [Coproducts.desc_comp, Coproducts.map_desc, Category.id_comp, e, operation_extend]
  have ext : (A).extend (k ≫ c) = S.map k ≫ (A).extend c := by
    simp only [KleisliTriple.ofMonad, Functor.map_comp, Category.assoc]
  change (ξ.app _ ≫ (A).extend (P.desc (S.η.app X) (runOperation σ X))) ≫ (A).extend f = _
  rw [Category.assoc, (A).extend_comp, show (A).extend f = b from rfl, bc, ext,
    parameter_map (P := P) (T := T) (H := H), ← ξ.toNatTrans.naturality_assoc]

private theorem extend_into_algebra {X Y W : C} (f : X ⟶ T.obj (P.sum Y (H.obj W)))
    {V : C} (c : P.sum Y (H.obj W) ⟶ S.obj V) :
    (M).extend (W := W) f ≫ ξ.app _ ≫ (A).extend c =
      ξ.app _ ≫ (A).extend
        (P.desc (f ≫ ξ.app (P.sum Y (H.obj W)) ≫ (A).extend c)
          (P.inr ≫ c)) := by
  let E := H.obj W
  let u := P.desc f (Exception.raise P T E Y)
  have e : (M).extend (W := W) f = (KleisliTriple.ofMonad T).extend u :=
    fibre_extend P f
  have h : (Exception.raise P T E Y ≫ ξ.app (P.sum Y E)) ≫ (A).extend c = P.inr ≫ c := by
    simp only [Exception.raise, Category.assoc, MonadHom.app_η_assoc, (A).unit_extend]
  calc
    (M).extend (W := W) f ≫ ξ.app _ ≫ (A).extend c =
        (ξ.app _ ≫ (A).extend (u ≫ ξ.app (P.sum Y E))) ≫ (A).extend c := by
      rw [e, ← Category.assoc, Proofs.map_extension ξ u]
    _ = _ := by
      rw [Category.assoc, (A).extend_comp]
      apply congrArg (fun d => ξ.app (P.sum X E) ≫ (A).extend d)
      change (P.desc f (Exception.raise P T E Y) ≫ ξ.app (P.sum Y E)) ≫ (A).extend c = _
      rw [Coproducts.desc_comp, Coproducts.desc_comp, h, Category.assoc]

private def ofExtension {U V : CategoryTheory.Monad C}
    (m : ∀ X, U.obj X ⟶ V.obj X)
    (hu : ∀ X, U.η.app X ≫ m X = V.η.app X)
    (he : ∀ {X Y} (f : X ⟶ U.obj Y),
      ((KleisliTriple.ofMonad U).extend f) ≫ m Y =
        m X ≫ (KleisliTriple.ofMonad V).extend (f ≫ m Y)) : U ⟶ V := by
  let natural : (U : C ⥤ C) ⟶ (V : C ⥤ C) := {
    app := m
    naturality := fun X Y f => by
      have e := he (f ≫ U.η.app Y)
      simpa only [KleisliTriple.ofMonad, Category.assoc, Functor.map_comp, hu,
        Monad.right_unit, Category.comp_id] using e }
  exact {
    toNatTrans := natural
    app_η := hu
    app_μ := fun X => by
      have e := he (𝟙 (U.obj X))
      change U.μ.app X ≫ m X = (U.map (m X) ≫ m (V.obj X)) ≫ V.μ.app X
      have n : U.map (m X) ≫ m (V.obj X) = m (U.obj X) ≫ V.map (m X) :=
        natural.naturality (m X)
      rw [n, Category.assoc]
      simpa only [KleisliTriple.ofMonad, Functor.map_id, Category.id_comp] using e }

variable (R : InitialResumptions (Exception.parametrized P T H))

theorem interpretation_roll (X : C) :
    R.roll X ≫ interpretation P ξ σ R X =
      ((M).parameter X).map (interpretation P ξ σ R X) ≫ interpretationAlgebra P ξ σ X :=
  R.fold_spec _

theorem interpretation_unit (X : C) :
    R.unit X ≫ interpretation P ξ σ R X = S.η.app X := by
  let e := interpretation P ξ σ R X
  let E := H.obj (S.obj X)
  change (Exception.unit P T (H.obj (R.obj X)) X ≫ R.roll X) ≫ e = _
  rw [Category.assoc, interpretation_roll]
  have h : Exception.unit P T (H.obj (R.obj X)) X ≫ ((M).parameter X).map e =
      Exception.unit P T E X :=
    Exception.change_unit P T (H.map e) X
  change Exception.unit P T (H.obj (R.obj X)) X ≫ ((M).parameter X).map e ≫
    ξ.app (P.sum X E) ≫ (A).extend _ = _
  rw [← Category.assoc, h]
  simp only [Exception.unit, Category.assoc, MonadHom.app_η_assoc, (A).unit_extend,
    Coproducts.inl_desc]

theorem interpretation_extend {X Y : C} (f : X ⟶ R.obj Y) :
    R.extend f ≫ interpretation P ξ σ R Y =
      interpretation P ξ σ R X ≫ (A).extend (f ≫ interpretation P ξ σ R Y) := by
  let e := R.extend f
  let p := interpretation P ξ σ R X
  let q := interpretation P ξ σ R Y
  let t := (A).extend (f ≫ q)
  let a := interpretationAlgebra P ξ σ Y
  let c := ξ.app (P.sum X (H.obj (S.obj Y))) ≫ (A).extend (P.desc (f ≫ q) (runOperation σ Y))
  have ep : (f ≫ R.out Y ≫ ((M).parameter Y).map q) ≫ a = f ≫ q := by
    rw [Category.assoc, Category.assoc, ← interpretation_roll, InitialResumptions.out_roll_assoc]
  have eL : R.roll X ≫ (e ≫ q) = ((M).parameter X).map (e ≫ q) ≫ c := by
    have spec : R.roll X ≫ e =
        ((M).parameter X).map e ≫ (M).extend (f ≫ R.out Y) ≫ R.roll Y := R.extend_spec f
    have fold : R.roll Y ≫ q = ((M).parameter Y).map q ≫ a := interpretation_roll P ξ σ R Y
    have pe := (M).parameter_extend (X := X) (Y := Y) q (f ≫ R.out Y)
    have ec : ((f ≫ R.out Y) ≫ ((M).parameter Y).map q) ≫
        ξ.app (P.sum Y (H.obj (S.obj Y))) ≫ (A).extend (P.desc (S.η.app Y) (runOperation σ Y)) =
          f ≫ q := by
      simpa only [a, interpretationAlgebra, Category.assoc] using ep
    calc
      R.roll X ≫ e ≫ q =
          ((M).parameter X).map e ≫ (M).extend (f ≫ R.out Y) ≫ ((M).parameter Y).map q ≫ a := by
        rw [← Category.assoc (R.roll X), spec]
        simp only [Category.assoc, fold]
      _ = ((M).parameter X).map e ≫ ((M).parameter X).map q ≫
          (M).extend (W := S.obj Y) ((f ≫ R.out Y) ≫ ((M).parameter Y).map q) ≫ a := by
        exact congrArg (((M).parameter X).map e ≫ ·)
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ a) pe.symm).trans (Category.assoc _ _ _)))
      _ = _ := by
        change _ ≫ _ ≫ _ ≫ ξ.app (P.sum Y (H.obj (S.obj Y))) ≫ (A).extend
          (P.desc (S.η.app Y) (runOperation σ Y)) = _
        rw [extend_into_algebra P ξ, ec, Coproducts.inr_desc]
        exact (Functor.map_comp_assoc _ _ _ _).symm
  have eR : R.roll X ≫ (p ≫ t) = ((M).parameter X).map (p ≫ t) ≫ c := by
    have e' : interpretationAlgebra P ξ σ X ≫ t = ((M).parameter X).map t ≫ c :=
      algebra_extend P ξ σ (f ≫ q)
    rw [← Category.assoc, interpretation_roll, Category.assoc, e']
    exact (Functor.map_comp_assoc _ _ _ _).symm
  exact (R.fold_unique c (e ≫ q) eL).trans (R.fold_unique c (p ≫ t) eR).symm


/-- The fold into the interpreting algebra is a monad morphism. -/
def interpretationHom : R.monad ⟶ S :=
  ofExtension (interpretation P ξ σ R) (interpretation_unit P ξ σ R) (fun f =>
    (congrArg (· ≫ interpretation P ξ σ R _) (R.monad_extend f)).trans
      (interpretation_extend P ξ σ R f))

omit S ξ σ in
private theorem base_extend {X Y : C} (f : X ⟶ R.obj Y) :
    liftBase P R X ≫ R.extend f = (KleisliTriple.ofMonad T).extend (f ≫ R.out Y) ≫ R.roll Y := by
  let E := H.obj (R.obj Y)
  let v := P.desc (f ≫ R.out Y) (Exception.raise P T E Y)
  let k := R.extend f
  have ext : (M).extend (W := R.obj Y) (f ≫ R.out Y) = T.map v ≫ T.μ.app (P.sum Y E) :=
    fibre_extend P (f ≫ R.out Y)
  have eq : P.inl (X := X) (Y := H.obj (R.obj X)) ≫ P.map (𝟙 X) (H.map k) ≫ v = f ≫ R.out Y := by
    simp [v, Coproducts.map, Category.assoc]
  change (T.map P.inl ≫ R.roll X) ≫ R.extend f = _
  rw [Category.assoc, R.extend_spec, parameter_map (P := P) (T := T) (H := H), ext]
  change T.map P.inl ≫ T.map (P.map (𝟙 X) (H.map k)) ≫ (T.map v ≫ T.μ.app _) ≫ R.roll Y =
    (T.map (f ≫ R.out Y) ≫ T.μ.app _) ≫ R.roll Y
  simp only [Category.assoc, ← Functor.map_comp_assoc, eq]

omit S ξ σ in
private theorem base_unit (X : C) : T.η.app X ≫ liftBase P R X = R.unit X := by
  change T.η.app X ≫ T.map P.inl ≫ R.roll X = (P.inl ≫ T.η.app _) ≫ R.roll X
  exact (T.η.naturality_assoc _ _).symm.trans (Category.assoc _ _ _).symm

omit S ξ σ in
/-- The canonical monad morphism from the base to inductive resumptions. -/
def baseEmbedding : T ⟶ R.monad :=
  ofExtension (liftBase P R) (base_unit P R) (fun {X Y} f => by
    change (KleisliTriple.ofMonad T).extend f ≫ liftBase P R Y = liftBase P R X ≫
      (R.monad.map (f ≫ liftBase P R Y) ≫ R.monad.μ.app Y)
    rw [R.monad_extend, base_extend]
    have e : liftBase P R Y ≫ R.out Y = T.map P.inl := by
      simp only [liftBase, Category.assoc, R.roll_out]
      exact Category.comp_id _
    rw [Category.assoc f, e]
    change (T.map f ≫ T.μ.app Y) ≫ T.map P.inl ≫ R.roll Y =
      (T.map (f ≫ T.map P.inl) ≫ T.μ.app _) ≫ R.roll Y
    have mul : T.μ.app Y ≫ T.map (P.inl (Y := H.obj (R.obj Y))) =
        T.map (T.map P.inl) ≫ T.μ.app (P.sum Y (H.obj (R.obj Y))) :=
      (T.μ.naturality (P.inl (Y := H.obj (R.obj Y)))).symm
    simp only [Category.assoc, ← reassoc_of% mul, Functor.map_comp])

omit S ξ σ in
private theorem roll_map {X Y : C} (f : X ⟶ Y) :
    R.roll X ≫ R.monad.map f =
      T.map (P.map f (H.map (R.monad.map f))) ≫ R.roll Y := by
  let L := ((M).obj (R.obj Y))
  let k : R.obj X ⟶ R.obj Y := R.monad.map f
  have e : R.roll X ≫ k = ((M).parameter X).map k ≫
      (M).extend ((f ≫ R.unit Y) ≫ R.out Y) ≫ R.roll Y := R.extend_spec _
  have ex : (M).extend (W := R.obj Y) ((f ≫ R.unit Y) ≫ R.out Y) = L.map f := by
    rw [Category.assoc, R.unit_out]
    change L.map (f ≫ L.η.app Y) ≫ L.μ.app Y = L.map f
    simp
  rw [e, ex, parameter_map (P := P) (T := T) (H := H)]
  have lm : L.map f = T.map (P.map f (𝟙 (H.obj (R.obj Y)))) :=
    Exception.family_map P T _ f
  rw [lm, ← Functor.map_comp_assoc]
  congr 2
  apply P.hom_ext
  · simp [Coproducts.map, Category.assoc]
  · simp [Coproducts.map, Category.assoc]
    rfl

omit S ξ σ in
private theorem raise_map {X Y E E' : C} (f : X ⟶ Y) (g : E ⟶ E') :
    Exception.raise P T E X ≫ T.map (P.map f g) = g ≫ Exception.raise P T E' Y := by
  simp [Exception.raise, ← T.η.naturality, Coproducts.map, Category.assoc]

omit S ξ σ in
private theorem step_natural {X Y : C} (f : X ⟶ Y) :
    H.map f ≫ liftStep P R Y = liftStep P R X ≫ R.monad.map f := by
  let k : R.obj X ⟶ R.obj Y := R.monad.map f
  have e : R.unit X ≫ k = f ≫ R.unit Y := (R.monad.η.naturality f).symm
  have h := raise_map (T := T) P f (H.map k)
  change H.map f ≫ H.map (R.unit Y) ≫ Exception.raise P T (H.obj (R.obj Y)) Y ≫ R.roll Y =
    (H.map (R.unit X) ≫ Exception.raise P T (H.obj (R.obj X)) X ≫ R.roll X) ≫ k
  rw [Category.assoc, Category.assoc, roll_map]
  change _ = H.map (R.unit X) ≫ Exception.raise P T _ X ≫ T.map (P.map f (H.map k)) ≫ R.roll Y
  rw [← Category.assoc (Exception.raise P T _ X), h, Category.assoc]
  exact ((H.map_comp_assoc f (R.unit Y) _).symm.trans
    ((congrArg (fun j => H.map j ≫ Exception.raise P T _ Y ≫ R.roll Y) e.symm).trans
      (H.map_comp_assoc (R.unit X) k _)))

omit S ξ σ in
/-- The operation generator of the inductive resumption monad. -/
def suspension : H ⟶ (R.monad : C ⥤ C) where
  app := liftStep P R
  naturality _ _ f := step_natural P R f


omit S ξ σ in
private theorem map_left_parameter {X W V : C} (k : W ⟶ V) :
    T.map (P.inl (X := X) (Y := H.obj W)) ≫ ((M).parameter X).map k =
      T.map (P.inl (X := X) (Y := H.obj V)) := by
  rw [parameter_map (P := P) (T := T) (H := H), ← Functor.map_comp]
  simp [Coproducts.map]

theorem interpretation_base (X : C) : liftBase P R X ≫ interpretation P ξ σ R X = ξ.app X := by
  let k := interpretation P ξ σ R X
  let E := H.obj (S.obj X)
  let l : X ⟶ P.sum X E := P.inl
  let d := P.desc (S.η.app X) (runOperation σ X)
  calc
    liftBase P R X ≫ k = T.map l ≫ ξ.app (P.sum X E) ≫ (A).extend d := by
      change (T.map P.inl ≫ R.roll X) ≫ k = _
      rw [Category.assoc, interpretation_roll, ← Category.assoc (T.map P.inl), map_left_parameter]
      rfl
    _ = ξ.app X ≫ (A).extend (l ≫ d) := by
      rw [ξ.toNatTrans.naturality_assoc]
      simp only [KleisliTriple.ofMonad, Functor.map_comp, Category.assoc]
    _ = _ := by
      have eq : l ≫ d = S.η.app X := P.inl_desc _ _
      rw [eq]
      exact (congrArg (ξ.app X ≫ ·) ((A).extend_unit X)).trans (Category.comp_id _)

theorem interpretation_step (X : C) : liftStep P R X ≫ interpretation P ξ σ R X = σ.app X := by
  let k := interpretation P ξ σ R X
  let E := H.obj (S.obj X)
  let d := P.desc (S.η.app X) (runOperation σ X)
  have h : Exception.raise P T (H.obj (R.obj X)) X ≫ ((M).parameter X).map k =
      H.map k ≫ Exception.raise P T E X := raise_map P (𝟙 X) (H.map k)
  have b : Exception.raise P T E X ≫ ξ.app (P.sum X E) ≫ (A).extend d = runOperation σ X := by
    have e : (S.η.app (P.sum X E)) ≫ (A).extend d = d := (A).unit_extend d
    simp only [Exception.raise, Category.assoc, MonadHom.app_η_assoc, e, d, Coproducts.inr_desc]
  calc
    liftStep P R X ≫ k = H.map (R.unit X) ≫ H.map k ≫ runOperation σ X := by
      change (H.map (R.unit X) ≫ Exception.raise P T _ X ≫ R.roll X) ≫ k = _
      have eq : R.roll X ≫ k = ((M).parameter X).map k ≫ interpretationAlgebra P ξ σ X :=
        interpretation_roll P ξ σ R X
      simp only [Category.assoc, eq]
      change H.map (R.unit X) ≫ Exception.raise P T _ X ≫ ((M).parameter X).map k ≫
        ξ.app (P.sum X E) ≫ (A).extend d = _
      rw [← Category.assoc (Exception.raise P T _ X), h]
      simp only [Category.assoc, b]
    _ = _ := by
      rw [← H.map_comp_assoc, interpretation_unit, runOperation, σ.naturality_assoc, S.right_unit,
        Category.comp_id]


omit S ξ σ in
private theorem step_flatten (X : C) :
    liftStep P R (R.obj X) ≫ R.extend (𝟙 (R.obj X)) =
      Exception.raise P T (H.obj (R.obj X)) X ≫ R.roll X := by
  let Y := R.obj X
  let k : R.obj Y ⟶ R.obj X := R.extend (𝟙 Y)
  let E := H.obj (R.obj X)
  have h : Exception.raise P T (H.obj (R.obj Y)) Y ≫ ((M).parameter Y).map k =
      H.map k ≫ Exception.raise P T E Y := raise_map P (𝟙 Y) (H.map k)
  have r : Exception.raise P T E Y ≫ (M).extend (W := R.obj X) ((𝟙 Y) ≫ R.out X) =
      Exception.raise P T E X := by
    rw [fibre_extend P]
    let a := P.desc ((𝟙 Y) ≫ R.out X) (Exception.raise P T E X)
    change (P.inr ≫ T.η.app (P.sum Y E)) ≫ (KleisliTriple.ofMonad T).extend a = _
    have e : T.η.app (P.sum Y E) ≫ (KleisliTriple.ofMonad T).extend a = a :=
      (KleisliTriple.ofMonad T).unit_extend a
    rw [Category.assoc, e]
    exact P.inr_desc _ _
  have ext_eq : R.roll Y ≫ k = ((M).parameter Y).map k ≫
      (M).extend ((𝟙 Y) ≫ R.out X) ≫ R.roll X := R.extend_spec _
  change (H.map (R.unit Y) ≫ Exception.raise P T (H.obj (R.obj Y)) Y ≫ R.roll Y) ≫ k = _
  simp only [Category.assoc, ext_eq]
  rw [← Category.assoc (Exception.raise P T _ Y), h]
  simp only [Category.assoc]
  rw [← Category.assoc (Exception.raise P T E Y), r, ← H.map_comp_assoc]
  have u : R.unit Y ≫ k = 𝟙 Y := R.unit_extend _
  rw [u, H.map_id, Category.id_comp]

omit S ξ σ in
theorem roll_generators (X : C) :
    let E := H.obj (R.obj X)
    let a := P.desc (R.unit X) (liftStep P R (R.obj X) ≫ R.extend (𝟙 (R.obj X)))
    R.roll X = liftBase P R (P.sum X E) ≫ R.extend a := by
  intro E a
  have e : a ≫ R.out X = T.η.app (P.sum X E) := by
    dsimp only [a]
    rw [Coproducts.desc_comp, R.unit_out, step_flatten, Category.assoc, R.roll_out]
    change P.desc (P.inl ≫ T.η.app (P.sum X E))
      ((P.inr ≫ T.η.app (P.sum X E)) ≫ 𝟙 (((M).obj (R.obj X)).obj X)) = _
    have h : (P.inr ≫ T.η.app (P.sum X E)) ≫ 𝟙 (((M).obj (R.obj X)).obj X) =
        P.inr ≫ T.η.app (P.sum X E) := Category.comp_id _
    rw [h, ← Coproducts.desc_comp, Coproducts.desc_inl_inr, Category.id_comp]
  rw [base_extend, e]
  have q := (KleisliTriple.ofMonad T).extend_unit (P.sum X E)
  change R.roll X = (KleisliTriple.ofMonad T).extend (T.η.app (P.sum X E)) ≫ R.roll X
  exact ((congrArg (· ≫ R.roll X) q).trans (Category.id_comp _)).symm

theorem interpretation_unique (m : R.monad ⟶ S)
    (hb : ∀ X, liftBase P R X ≫ m.app X = ξ.app X)
    (hs : ∀ X, liftStep P R X ≫ m.app X = σ.app X)
    (X : C) : m.app X = interpretation P ξ σ R X := by
  let Y := R.obj X
  let E := H.obj Y
  let v : Y ⟶ S.obj X := m.app X
  let a := P.desc (R.unit X) (liftStep P R Y ≫ R.extend (𝟙 Y))
  let d := interpretationAlgebra P ξ σ X
  have bind : R.extend a ≫ v = m.app (P.sum X E) ≫ (A).extend (a ≫ v) :=
    (congrArg (· ≫ v) (R.monad_extend a)).symm.trans (Proofs.map_extension m a)
  have step_eq : (liftStep P R Y ≫ R.extend (𝟙 Y)) ≫ v = H.map v ≫ runOperation σ X := by
    have he : R.extend (𝟙 Y) ≫ v = m.app Y ≫ (A).extend (𝟙 Y ≫ v) :=
      (congrArg (· ≫ v) (R.monad_extend (𝟙 Y))).symm.trans (Proofs.map_extension m (𝟙 Y))
    rw [Category.assoc, he, ← Category.assoc (liftStep P R Y), hs, Category.id_comp]
    exact σ.naturality_assoc v (S.μ.app X) |>.symm
  have coeff : a ≫ v = P.desc (S.η.app X) (H.map v ≫ runOperation σ X) := by
    dsimp only [a]
    rw [Coproducts.desc_comp, step_eq]
    exact congrArg (P.desc · (H.map v ≫ runOperation σ X)) (m.app_η X)
  have e : R.roll X ≫ v = ((M).parameter X).map v ≫ d := by
    rw [roll_generators P R X]
    change (liftBase P R (P.sum X E) ≫ R.extend a) ≫ v = _
    rw [Category.assoc, bind, ← Category.assoc (liftBase P R (P.sum X E)), hb, coeff,
      parameter_map (P := P) (T := T) (H := H)]
    let j := P.map (𝟙 X) (H.map v)
    let c := P.desc (S.η.app X) (runOperation σ X)
    change ξ.app (P.sum X E) ≫ (A).extend (P.desc (S.η.app X) (H.map v ≫ runOperation σ X)) =
      T.map j ≫ ξ.app _ ≫ (A).extend c
    have j_eq : j ≫ c = P.desc (S.η.app X) (H.map v ≫ runOperation σ X) := by
      simp [j, c]
    rw [ξ.toNatTrans.naturality_assoc, ← j_eq]
    simp only [KleisliTriple.ofMonad, Functor.map_comp, Category.assoc]
    rfl
  exact R.fold_unique d v e


theorem interpretationHom_app (X : C) :
    (interpretationHom P ξ σ R).app X = interpretation P ξ σ R X := by
  unfold interpretationHom ofExtension
  rfl

omit S ξ σ in
theorem baseEmbedding_app (X : C) : (baseEmbedding P R).app X = liftBase P R X := by
  unfold baseEmbedding ofExtension
  rfl

omit S ξ σ in
theorem suspension_app (X : C) : (suspension P R).app X = liftStep P R X := by
  unfold suspension
  rfl

theorem interpretation_universal :
    ∃! m : R.monad ⟶ S, suspension P R ≫ m.toNatTrans = σ ∧ baseEmbedding P R ≫ m = ξ := by
  let m := interpretationHom P ξ σ R
  refine ⟨m, ⟨?_, ?_⟩, ?_⟩
  · apply NatTrans.ext
    funext X
    change (suspension P R).app X ≫ m.app X = σ.app X
    rw [suspension_app, interpretationHom_app]
    exact interpretation_step P ξ σ R X
  · apply MonadHom.ext
    funext X
    change (baseEmbedding P R).app X ≫ m.app X = ξ.app X
    rw [baseEmbedding_app, interpretationHom_app]
    exact interpretation_base P ξ σ R X
  · rintro n ⟨ns, nb⟩
    have b (X : C) : liftBase P R X ≫ n.app X = ξ.app X := by
      have e := congrArg (fun k : T ⟶ S => k.app X) nb
      change (baseEmbedding P R).app X ≫ n.app X = ξ.app X at e
      simpa only [baseEmbedding_app] using e
    have s (X : C) : liftStep P R X ≫ n.app X = σ.app X := by
      have e := congrArg (fun k => NatTrans.app k X) ns
      change (suspension P R).app X ≫ n.app X = σ.app X at e
      simpa only [suspension_app] using e
    apply MonadHom.ext
    funext X
    rw [interpretationHom_app]
    exact interpretation_unique P ξ σ R n b s X


omit S ξ σ in
theorem resumption_free :
    (monadBimodule C).IsFreeExtension (suspension P R) (baseEmbedding P R) := by
  intro U τ ρ
  simp only [monadBimodule_post]
  exact interpretation_universal P ρ τ R

/-- The identity monad is the initial object of the ordinary monad category. -/
def identity_initial : IsInitial (CategoryTheory.Monad.id C) :=
  IsInitial.ofUniqueHom identityMonadMap (fun U m => MonadHom.ext (funext fun X => by
    have h := m.app_η X
    change 𝟙 X ≫ m.app X = U.η.app X at h
    exact (Category.id_comp _).symm.trans h))

omit T S ξ σ R in
theorem resumption_freeOn (R₀ : InitialResumptions (Exception.parametrized P (CategoryTheory.Monad.id C) H)) :
    (monadBimodule C).IsFreeObject (suspension P R₀) := by
  let i := identity_initial (C := C)
  have e : baseEmbedding P R₀ = i.to R₀.monad := i.hom_ext _ _
  exact (isFreeExtension_initial_iff (O := monadBimodule C) i (suspension P R₀)).mp (e ▸ resumption_free P R₀)

end Silmaril.Calco2019.Proofs.InductiveResumptionFree
