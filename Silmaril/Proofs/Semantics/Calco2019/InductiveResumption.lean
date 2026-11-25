module

public import Silmaril.Semantics.Calco2019.InductiveResumption.Defs
public import Silmaril.Semantics.Calco2019.ResumptionThms

public section

universe u v

namespace Silmaril.Calco2019.Proofs.InductiveResumption

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

variable {C : Type u} [Category.{v} C] {M : ParametrizedMonad C}
  (R : InitialResumptions M)

theorem fold_spec {X S : C} (a : (M.obj S).obj X ⟶ S) :
    R.roll X ≫ R.fold a = (M.parameter X).map (R.fold a) ≫ a :=
  ((R.initial X).to (⟨S, a⟩ : Algebra (M.parameter X))).h.symm

theorem fold_unique {X S : C} (a : (M.obj S).obj X ⟶ S) (k : R.obj X ⟶ S)
    (hk : R.roll X ≫ k = (M.parameter X).map k ≫ a) : k = R.fold a := by
  let b : Algebra (M.parameter X) := ⟨S, a⟩
  let f : R.algebra X ⟶ b := ⟨k, hk.symm⟩
  exact congrArg Algebra.Hom.f ((R.initial X).hom_ext f ((R.initial X).to b))

@[reassoc]
theorem out_roll (X : C) : R.out X ≫ R.roll X = 𝟙 (R.obj X) :=
  Algebra.Initial.left_inv (R.initial X)

@[reassoc]
theorem roll_out (X : C) : R.roll X ≫ R.out X = 𝟙 ((M.obj (R.obj X)).obj X) :=
  Algebra.Initial.right_inv (R.initial X)

@[reassoc]
theorem extend_spec {X Y : C} (f : X ⟶ R.obj Y) :
    R.roll X ≫ R.extend f =
      (M.parameter X).map (R.extend f) ≫ M.extend (f ≫ R.out Y) ≫ R.roll Y :=
  fold_spec R (R.extensionAlgebra f)

theorem extend_unique {X Y : C} (f : X ⟶ R.obj Y) (k : R.obj X ⟶ R.obj Y)
    (hk : R.roll X ≫ k = (M.parameter X).map k ≫ M.extend (f ≫ R.out Y) ≫ R.roll Y) :
    k = R.extend f :=
  fold_unique R (R.extensionAlgebra f) k hk

theorem extend_out {X Y : C} (f : X ⟶ R.obj Y) :
    R.extend f ≫ R.out Y =
      R.out X ≫ (M.parameter X).map (R.extend f) ≫ M.extend (f ≫ R.out Y) := by
  calc
    _ = (R.out X ≫ R.roll X) ≫ R.extend f ≫ R.out Y := by rw [out_roll, Category.id_comp]
    _ = _ := by
      simp only [Category.assoc, extend_spec_assoc, roll_out, Category.comp_id]

theorem unit_out (X : C) : R.unit X ≫ R.out X = (M.obj (R.obj X)).η.app X := by
  unfold InitialResumptions.unit
  rw [Category.assoc, roll_out, Category.comp_id]

theorem unit_extend {X Y : C} (f : X ⟶ R.obj Y) : R.unit X ≫ R.extend f = f := by
  let u := f ≫ R.out Y
  have e : (M.obj (R.obj X)).η.app X ≫ (M.parameter X).map (R.extend f) =
      (M.obj (R.obj Y)).η.app X := (M.map (R.extend f)).app_η X
  calc
    R.unit X ≫ R.extend f =
        (M.obj (R.obj X)).η.app X ≫ (M.parameter X).map (R.extend f) ≫ M.extend u ≫ R.roll Y := by
      simp only [InitialResumptions.unit, Category.assoc, extend_spec]
      rfl
    _ = ((M.obj (R.obj Y)).η.app X ≫ M.extend u) ≫ R.roll Y := by
      rw [← Category.assoc, e, Category.assoc]
    _ = _ := by
      rw [show (M.obj (R.obj Y)).η.app X ≫ M.extend u = u from
        (KleisliTriple.ofMonad (M.obj (R.obj Y))).unit_extend u]
      simp only [u, Category.assoc, out_roll, Category.comp_id]

theorem extend_unit (X : C) : R.extend (R.unit X) = 𝟙 (R.obj X) := by
  symm
  apply extend_unique R
  rw [Category.comp_id, Functor.map_id, Category.id_comp, unit_out]
  exact (Category.id_comp (R.roll X)).symm.trans
    (congrArg (· ≫ R.roll X) ((KleisliTriple.ofMonad (M.obj (R.obj X))).extend_unit X).symm)

theorem extend_comp {X Y Z : C} (f : X ⟶ R.obj Y) (g : Y ⟶ R.obj Z) :
    R.extend f ≫ R.extend g = R.extend (f ≫ R.extend g) := by
  let e := R.extend f
  let k := R.extend g
  let u := f ≫ R.out Y
  let v := g ≫ R.out Z
  let A := M.parameter X
  let B := M.parameter Y
  have pe : M.extend u ≫ B.map k = A.map k ≫ M.extend (u ≫ B.map k) :=
    (M.parameter_extend k u).symm
  have pc : M.extend (u ≫ B.map k) ≫ M.extend v =
      M.extend ((u ≫ B.map k) ≫ M.extend v) :=
    (KleisliTriple.ofMonad (M.obj (R.obj Z))).extend_comp _ _
  have pu : (u ≫ B.map k) ≫ M.extend v = (f ≫ k) ≫ R.out Z := by
    simp only [u, B, Category.assoc]
    exact congrArg (f ≫ ·) (extend_out R g).symm
  apply extend_unique R
  calc
    R.roll X ≫ e ≫ k =
        A.map e ≫ M.extend u ≫ B.map k ≫ M.extend v ≫ R.roll Z := by
      simp only [e, k, u, v, A, B, extend_spec_assoc, extend_spec]
    _ = (A.map e ≫ A.map k) ≫ (M.extend (u ≫ B.map k) ≫ M.extend v) ≫ R.roll Z := by
      simp only [Category.assoc, reassoc_of% pe]
    _ = _ := by
      rw [pc, pu, ← A.map_comp]

end Silmaril.Calco2019.Proofs.InductiveResumption
