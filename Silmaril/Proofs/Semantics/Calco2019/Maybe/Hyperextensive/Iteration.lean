module

public import Silmaril.Semantics.Calco2019.Maybe.Hyperextensive.Iteration.Defs
import Silmaril.Proofs.Semantics.Calco2019.Maybe.Hyperextensive
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Maybe.Proofs

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

private instance : Countable (Option ℕ) :=
  ⟨⟨fun i => i.elim 0 (· + 1), by intro i j h; cases i <;> cases j <;> simp_all⟩⟩

variable {C : Type u} [Category.{v} C] [Hyperextensive C] {P : Coproducts C}
  {E X Y : C} (E₀ : IsTerminal E) (f : X ⟶ P.sum (P.sum Y E) X)

theorem solve_finite (n : ℕ) :
    (decompose f).finiteIn n ≫ solve E₀ f = (decompose f).returnAt n :=
  Cofan.IsColimit.fac (decompose f).isColimit _ (some n)

theorem solve_residual :
    (decompose f).residualIn ≫ solve E₀ f = failure E₀ :=
  Cofan.IsColimit.fac (decompose f).isColimit _ none

theorem solve_fixpoint :
    f ≫ P.desc (𝟙 _) (solve E₀ f) = solve E₀ f := by
  let D := decompose f
  refine Cofan.IsColimit.hom_ext D.isColimit _ _ (fun i => ?_)
  cases i with
  | none =>
    change D.residualIn ≫ (f ≫ P.desc (𝟙 _) (solve E₀ f)) =
      D.residualIn ≫ solve E₀ f
    rw [← Category.assoc, D.residual_eq, Category.assoc, Category.assoc, P.inr_desc]
    change D.residualStep ≫ ((decompose f).residualIn ≫ solve E₀ f) =
      (decompose f).residualIn ≫ solve E₀ f
    rw [solve_residual]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ P.inr) (E₀.hom_ext _ _))
  | some n =>
    change D.finiteIn n ≫ (f ≫ P.desc (𝟙 _) (solve E₀ f)) =
      (decompose f).finiteIn n ≫ solve E₀ f
    rw [solve_finite, ← Category.assoc]
    cases n with
    | zero => rw [D.zero_eq, Category.assoc, P.inl_desc, Category.comp_id]; rfl
    | succ n =>
      rw [D.succ_eq, Category.assoc, Category.assoc, P.inr_desc]
      change D.advance n ≫ ((decompose f).finiteIn n ≫ solve E₀ f) = _
      rw [solve_finite]
      rfl

private theorem invariant_disjoint {A : C} (i : A ⟶ X) (k : A ⟶ A)
    (eq : i ≫ f = k ≫ i ≫ P.inr) (D : LoopDecomposition f) (n : ℕ) :
    Disjoint i (D.finiteIn n) := by
  induction n with
  | zero =>
    intro W a b same
    have e := congrArg (· ≫ f) same
    simp only [Category.assoc, eq, D.zero_eq] at e
    have he : (a ≫ k ≫ i) ≫ P.inr = (b ≫ D.result) ≫ P.inl := by
      simpa only [Category.assoc] using e
    exact hyperextensive_disjoint_binary
      (BinaryCofan.isColimitFlip (P.isColimit (P.sum Y E) X)) (a ≫ k ≫ i) (b ≫ D.result) he
  | succ n ih =>
    intro W a b same
    have e := congrArg (· ≫ f) same
    simp only [Category.assoc, eq, D.succ_eq] at e
    let _ : Mono (P.inr (X := P.sum Y E) (Y := X)) :=
      hyperextensive_mono_left (BinaryCofan.isColimitFlip (P.isColimit (P.sum Y E) X))
    apply ih (a ≫ k) (b ≫ D.advance n)
    exact (cancel_mono (P.inr (X := P.sum Y E) (Y := X))).mp
      (by simpa only [Category.assoc] using e)

theorem solve_invariant {A : C} (i : A ⟶ X) (k : A ⟶ A)
    (eq : i ≫ f = k ≫ i ≫ P.inr) :
    i ≫ solve E₀ f = failure E₀ := by
  let D := decompose f
  let d := (Hyperextensive.universal _ D.isColimit i).some
  apply Cofan.IsColimit.hom_ext d.colimit
  intro j
  cases j with
  | none =>
    have w : d.incl none ≫ i = d.map none ≫ D.residualIn := (d.pullback none).w
    change d.incl none ≫ (i ≫ solve E₀ f) = d.incl none ≫ failure E₀
    rw [← Category.assoc, w, Category.assoc]
    change d.map none ≫ ((decompose f).residualIn ≫ solve E₀ f) = _
    rw [solve_residual]
    change d.map none ≫ (E₀.from _ ≫ P.inr) = d.incl none ≫ (E₀.from _ ≫ P.inr)
    simp only [← Category.assoc]
    exact congrArg (· ≫ P.inr) (E₀.hom_ext _ _)
  | some n =>
    have w : d.incl (some n) ≫ i = d.map (some n) ≫ D.finiteIn n := (d.pullback (some n)).w
    obtain ⟨empty⟩ := invariant_disjoint f i k eq D n (d.incl (some n)) (d.map (some n)) w
    exact empty.hom_ext _ _

theorem solve_canonical : Canonical E₀ f (solve E₀ f) :=
  ⟨solve_fixpoint E₀ f, fun {_} i k eq => solve_invariant E₀ f i k eq⟩

omit [Hyperextensive C] in
theorem canonical_finite {s : X ⟶ P.sum Y E} (hs : Canonical E₀ f s)
    (D : LoopDecomposition f) (n : ℕ) : D.finiteIn n ≫ s = D.returnAt n := by
  induction n with
  | zero =>
    calc
      _ = D.finiteIn 0 ≫ (f ≫ P.desc (𝟙 _) s) := congrArg (D.finiteIn 0 ≫ ·) hs.1.symm
      _ = _ := by rw [← Category.assoc, D.zero_eq, Category.assoc, P.inl_desc, Category.comp_id]; rfl
  | succ n ih =>
    calc
      _ = D.finiteIn (n + 1) ≫ (f ≫ P.desc (𝟙 _) s) := congrArg (D.finiteIn (n + 1) ≫ ·) hs.1.symm
      _ = _ := by rw [← Category.assoc, D.succ_eq, Category.assoc, Category.assoc,
                     P.inr_desc, ih]; rfl

theorem solve_unique {s : X ⟶ P.sum Y E} (hs : Canonical E₀ f s) :
    s = solve E₀ f := by
  let D := decompose f
  apply Cofan.IsColimit.hom_ext D.isColimit
  intro j
  cases j with
  | none => exact (hs.2 D.residualIn D.residualStep D.residual_eq).trans (solve_residual E₀ f).symm
  | some n => exact (canonical_finite E₀ f hs D n).trans (solve_finite E₀ f n).symm


theorem solve_uniform {A : C} (g : A ⟶ P.sum (P.sum Y E) A) (h : A ⟶ X)
    (comm : h ≫ f = g ≫ P.map (𝟙 (P.sum Y E)) h) :
    h ≫ solve E₀ f = solve E₀ g := by
  apply solve_unique E₀ g
  constructor
  · calc
      _ = g ≫ P.map (𝟙 (P.sum Y E)) h ≫ P.desc (𝟙 _) (solve E₀ f) := by
        rw [P.map_desc, Category.id_comp]
      _ = h ≫ (f ≫ P.desc (𝟙 _) (solve E₀ f)) := by
        rw [← Category.assoc, ← comm, Category.assoc]
      _ = _ := congrArg (h ≫ ·) (solve_fixpoint E₀ f)
  · intro B i k eq
    rw [← Category.assoc]
    apply solve_invariant E₀ f (i ≫ h) k
    rw [Category.assoc, comm, ← Category.assoc, eq, Category.assoc, Category.assoc]
    simp [Coproducts.map]

theorem solve_natural {Z : C} (t : P.sum Y E ⟶ P.sum Z E)
    (pres : P.inr ≫ t = P.inr) :
    solve E₀ f ≫ t = solve E₀ (f ≫ P.map t (𝟙 X)) := by
  let D := decompose f
  let g := f ≫ P.map t (𝟙 X)
  let D' : LoopDecomposition g :=
    { finite := D.finite
      residual := D.residual
      finiteIn := D.finiteIn
      residualIn := D.residualIn
      result := D.result ≫ t
      advance := D.advance
      residualStep := D.residualStep
      zero_eq := by
        change D.finiteIn 0 ≫ (f ≫ P.map t (𝟙 X)) = _
        rw [← Category.assoc, D.zero_eq]
        simp [Category.assoc, Coproducts.map]
      succ_eq := fun n => by
        change D.finiteIn (n + 1) ≫ (f ≫ P.map t (𝟙 X)) = _
        rw [← Category.assoc, D.succ_eq]
        simp [Category.assoc, Coproducts.map]
      residual_eq := by
        change D.residualIn ≫ (f ≫ P.map t (𝟙 X)) = _
        rw [← Category.assoc, D.residual_eq]
        simp [Category.assoc, Coproducts.map]
      isColimit := D.isColimit }
  have result (n : ℕ) : D.returnAt n ≫ t = D'.returnAt n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (D.advance n ≫ D.returnAt n) ≫ t = D.advance n ≫ D'.returnAt n
      rw [Category.assoc, ih]
  change solve E₀ f ≫ t = solve E₀ g
  apply Cofan.IsColimit.hom_ext D.isColimit
  intro i
  cases i with
  | none =>
    change (decompose f).residualIn ≫ (solve E₀ f ≫ t) = D'.residualIn ≫ solve E₀ g
    rw [← Category.assoc, solve_residual, solve_invariant E₀ g D'.residualIn D'.residualStep D'.residual_eq]
    exact (Category.assoc _ _ _).trans (congrArg (E₀.from _ ≫ ·) pres)
  | some n =>
    change (decompose f).finiteIn n ≫ (solve E₀ f ≫ t) = D'.finiteIn n ≫ solve E₀ g
    rw [← Category.assoc, solve_finite, canonical_finite E₀ g (solve_canonical E₀ g) D' n]
    exact result n


section Kleisli

variable {E : C} (E₀' : IsTerminal E)

open Silmaril.Calco2019.Proofs

omit [Hyperextensive C] in
private theorem map_eq {A B : C} (h : A ⟶ B) :
    (monad P E).map h = P.map h (𝟙 E) :=
  Exception.family_map P (CategoryTheory.Monad.id C) E h

omit [Hyperextensive C] in
theorem comp_eq {A B D : Kleisli (monad P E)} (a : A ⟶ B) (b : B ⟶ D) :
    (a ≫ b).of = a.of ≫ P.desc b.of P.inr := by
  have ext : (monad P E).map b.of ≫ (monad P E).μ.app D.of = P.desc b.of P.inr := by
    refine (Exception.family_extend P (CategoryTheory.Monad.id C) E b.of).trans ?_
    change (P.desc b.of (P.inr ≫ 𝟙 (P.sum D.of E)) ≫ 𝟙 _) = _
    rw [Category.comp_id]
    exact congrArg (P.desc b.of) (Category.comp_id _)
  exact congrArg (a.of ≫ ·) ext

omit [Hyperextensive C] in
private theorem pure_id (Y : Kleisli (monad P E)) :
    (show Kleisli.Hom Y Y from 𝟙 Y).of = P.inl :=
  Category.comp_id _

omit [Hyperextensive C] in
private theorem pure_inl {Y Z : Kleisli (monad P E)} :
    ((P.kleisli (monad P E)).inl (X := Y) (Y := Z)).of = P.inl ≫ P.inl := by
  change P.inl ≫ (P.inl ≫ 𝟙 _) = _
  simp

omit [Hyperextensive C] in
private theorem pure_inr {Y Z : Kleisli (monad P E)} :
    ((P.kleisli (monad P E)).inr (X := Y) (Y := Z)).of = P.inr ≫ P.inl := by
  change P.inr ≫ (P.inl ≫ 𝟙 _) = _
  simp

omit [Hyperextensive C] in
theorem expand_fixpoint {X Y : Kleisli (monad P E)}
    (b : X ⟶ (P.kleisli (monad P E)).sum Y X) (s : X ⟶ Y) :
    (b ≫ (P.kleisli (monad P E)).desc (𝟙 Y) s).of =
      (b.of ≫ Exception.rearrange P E) ≫ P.desc (𝟙 _) s.of := by
  rw [comp_eq, kleisli_desc_of, pure_id, Category.assoc]
  apply congrArg (b.of ≫ ·)
  rw [Exception.rearrange, P.desc_comp]
  apply P.hom_ext
  · apply P.hom_ext <;> simp
  · simp

include E₀' in
theorem kleisli_fixpoint {X Y : Kleisli (monad P E)}
    (b : X ⟶ (P.kleisli (monad P E)).sum Y X) :
    Guardedness.IsFixpoint b (kleisliArrow (loop E₀' b.of)) := by
  apply Kleisli.hom_ext
  rw [expand_fixpoint]
  exact solve_fixpoint E₀' (b.of ≫ Exception.rearrange P E)

omit [Hyperextensive C] in
private theorem normalize_map {X Y Z : Kleisli (monad P E)}
    (b : X ⟶ (P.kleisli (monad P E)).sum Y X) (k : Y ⟶ Z) :
    (b ≫ (P.kleisli (monad P E)).map k (𝟙 X)).of ≫ Exception.rearrange P E =
      (b.of ≫ Exception.rearrange P E) ≫ P.map (P.desc k.of P.inr) (𝟙 X.of) := by
  let Q := P.kleisli (monad P E)
  change (b ≫ Q.desc (k ≫ Q.inl) (𝟙 X ≫ Q.inr)).of ≫ _ = _
  rw [Category.id_comp]
  have d := kleisli_desc_of P (monad P E) (k ≫ Q.inl) (Q.inr (X := Z) (Y := X))
  have left := comp_eq k (Q.inl (Y := X) (X := Z))
  have left' : (k ≫ Q.inl (Y := X) (X := Z)).of = k.of ≫ P.desc (P.inl ≫ P.inl) P.inr :=
    left.trans (congrArg (fun t => k.of ≫ P.desc t P.inr) pure_inl)
  have details :
      (Q.desc (k ≫ Q.inl) (Q.inr (X := Z) (Y := X))).of =
        P.desc (k.of ≫ P.desc (P.inl ≫ P.inl) P.inr) (P.inr ≫ P.inl) :=
    d.trans (congrArg₂ P.desc left' pure_inr)
  have c := (comp_eq b (Q.desc (k ≫ Q.inl) (Q.inr (X := Z) (Y := X)))).trans
    (congrArg (fun p => b.of ≫ P.desc p P.inr) details)
  refine (congrArg (· ≫ Exception.rearrange P E) c).trans ?_
  rw [Category.assoc, Category.assoc]
  apply congrArg (b.of ≫ ·)
  simp only [Exception.rearrange, P.desc_comp]
  apply P.hom_ext
  · rw [P.inl_desc, P.inl_desc]
    apply P.hom_ext
    · simp [Coproducts.map]
      exact congrArg (k.of ≫ ·) (P.hom_ext (by simp) (by simp))
    · simp [Coproducts.map]
  · simp [Coproducts.map]

include E₀' in
theorem kleisli_natural {X Y Z : Kleisli (monad P E)}
    (b : X ⟶ (P.kleisli (monad P E)).sum Y X) (k : Y ⟶ Z) :
    kleisliArrow (loop E₀' (b ≫ (P.kleisli (monad P E)).map k (𝟙 X)).of) =
      (kleisliArrow (loop E₀' b.of) : X ⟶ Y) ≫ k := by
  apply Kleisli.hom_ext
  change solve E₀' ((b ≫ _).of ≫ Exception.rearrange P E) = _
  rw [normalize_map]
  exact (solve_natural E₀' (b.of ≫ Exception.rearrange P E) (P.desc k.of P.inr)
    (P.inr_desc _ _)).symm.trans ((comp_eq (kleisliArrow (loop E₀' b.of)) k).symm)

include E₀' in
theorem kleisli_uniform {X A : C} {Y : Kleisli (monad P E)}
    (b : Kleisli.mk (monad P E) X ⟶ (P.kleisli (monad P E)).sum Y (Kleisli.mk (monad P E) X))
    (c : Kleisli.mk (monad P E) A ⟶ (P.kleisli (monad P E)).sum Y (Kleisli.mk (monad P E) A))
    (h : A ⟶ X)
    (comm : (Kleisli.Adjunction.toKleisli (monad P E)).map h ≫ b =
      c ≫ (P.kleisli (monad P E)).map (𝟙 Y) ((Kleisli.Adjunction.toKleisli (monad P E)).map h)) :
    (Kleisli.Adjunction.toKleisli (monad P E)).map h ≫ kleisliArrow (loop E₀' b.of) =
      kleisliArrow (loop E₀' c.of) := by
  let J := Kleisli.Adjunction.toKleisli (monad P E)
  have e := congrArg Kleisli.Hom.of comm
  change (J.map h ≫ b).of = (c ≫ (P.kleisli (monad P E)).map (𝟙 Y) (J.map h)).of at e
  have q : (P.kleisli (monad P E)).map (𝟙 Y) (J.map h) = J.map (P.map (𝟙 Y.of) h) := by
    have same : J.map (𝟙 Y.of) = (𝟙 Y) := J.map_id _
    exact (congrArg (fun x => (P.kleisli (monad P E)).map x (J.map h)) same.symm).trans
      (kleisli_map_pure (P := P) (monad P E) _ _)
  rw [q, pure_comp_of, comp_pure_of, map_eq] at e
  have retarget :
    P.map (P.map (𝟙 Y.of) h) (𝟙 E) ≫ Exception.rearrange P E =
      Exception.rearrange P E ≫ P.map (𝟙 (P.sum Y.of E)) h := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [Coproducts.map, Exception.rearrange]
    · simp [Coproducts.map, Exception.rearrange]
  apply Kleisli.hom_ext
  rw [pure_comp_of]
  apply solve_uniform E₀'
  rw [← Category.assoc, e, Category.assoc, retarget, Category.assoc]

end Kleisli

end Silmaril.Calco2019.Maybe.Proofs
