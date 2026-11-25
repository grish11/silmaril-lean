module

public import Silmaril.Semantics.Calco2019.Maybe.Hyperextensive.Iteration.Defs
import Silmaril.Proofs.Semantics.Calco2019.Maybe.Hyperextensive
import Silmaril.Proofs.Semantics.Calco2019.Maybe.Hyperextensive.Iteration

public section

universe u v

namespace Silmaril.Calco2019.Maybe.Proofs

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

section PartialResults

variable {C : Type u} [Category.{v} C] {P : Coproducts C} {E X Y : C}

/-- Partial results are ordered by agreement on every successful observation. -/
private def Below (f g : X ⟶ P.sum Y E) : Prop :=
  ∀ ⦃A : C⦄ (i : A ⟶ X) (y : A ⟶ Y), i ≫ f = y ≫ P.inl → i ≫ g = y ≫ P.inl

private theorem below_refl (f : X ⟶ P.sum Y E) : Below f f := fun {_} _ _ e => e

private theorem below_trans {f g h : X ⟶ P.sum Y E} (fg : Below f g) (gh : Below g h) :
    Below f h := fun {_} i y e => gh i y (fg i y e)

private theorem below_precomp {A : C} {f g : X ⟶ P.sum Y E} (i : A ⟶ X) (fg : Below f g) :
    Below (i ≫ f) (i ≫ g) := by
  intro B j y hj
  rw [← Category.assoc] at hj ⊢
  exact fg (j ≫ i) y hj

variable [Hyperextensive C]

private instance : Countable (Option ℕ) :=
  ⟨⟨fun i => i.elim 0 (· + 1), by intro i j h; cases i <;> cases j <;> simp_all⟩⟩

private theorem below_failure (E₀ : IsTerminal E) (f : X ⟶ P.sum Y E) :
    Below (failure E₀) f := by
  intro A i y e
  have eq : (i ≫ E₀.from X) ≫ P.inr = y ≫ P.inl := (Category.assoc _ _ _).trans e
  obtain ⟨empty⟩ := hyperextensive_disjoint_binary
    (BinaryCofan.isColimitFlip (P.isColimit Y E)) (i ≫ E₀.from X) y eq
  exact empty.hom_ext _ _

private theorem below_on_cofan {I : Type} [Countable I] {F : I → C} (c : Cofan F)
    (hc : IsColimit c) {f g : c.pt ⟶ P.sum Y E} (h : ∀ i, Below (c.inj i ≫ f) (c.inj i ≫ g)) :
    Below f g := by
  intro A i y e
  let s := (Hyperextensive.universal c hc i).some
  apply Cofan.IsColimit.hom_ext s.colimit
  intro n
  have eq : s.map n ≫ (c.inj n ≫ f) = (s.incl n ≫ y) ≫ P.inl := by
    rw [← Category.assoc, ← (s.pullback n).w, Category.assoc, e, Category.assoc]
  have same := h n (s.map n) (s.incl n ≫ y) eq
  rw [← Category.assoc, ← (s.pullback n).w, Category.assoc, Category.assoc] at same
  exact same

private theorem below_antisymm (E₀ : IsTerminal E) {f g : X ⟶ P.sum Y E}
    (fg : Below f g) (gf : Below g f) : f = g := by
  let c := (hyperextensive_pullback_binary (P.isColimit Y E) f).some
  apply Cofan.IsColimit.hom_ext c.colimit
  intro n
  cases n with
  | left =>
    have e : c.incl .left ≫ f = c.map .left ≫ P.inl := (c.pullback .left).w
    exact e.trans (fg (c.incl .left) (c.map .left) e).symm
  | right =>
    change c.incl .right ≫ f = c.incl .right ≫ g
    let d := (hyperextensive_pullback_binary (P.isColimit Y E) (c.incl .right ≫ g)).some
    have e : c.incl .right ≫ f = c.map .right ≫ P.inr := (c.pullback .right).w
    apply Cofan.IsColimit.hom_ext d.colimit
    intro m
    cases m with
    | left =>
      have r : d.incl .left ≫ (c.incl .right ≫ g) = d.map .left ≫ P.inl :=
        (d.pullback .left).w
      have l := gf (d.incl .left ≫ c.incl .right) (d.map .left)
        ((Category.assoc _ _ _).trans r)
      have fail : (d.incl .left ≫ c.map .right) ≫ P.inr = d.map .left ≫ P.inl := by
        rw [Category.assoc, ← e, ← Category.assoc, l]
      obtain ⟨empty⟩ := hyperextensive_disjoint_binary
        (BinaryCofan.isColimitFlip (P.isColimit Y E))
        (d.incl .left ≫ c.map .right) (d.map .left) fail
      exact empty.hom_ext _ _
    | right =>
      change d.incl .right ≫ (c.incl .right ≫ f) = d.incl .right ≫ (c.incl .right ≫ g)
      have r : d.incl .right ≫ (c.incl .right ≫ g) = d.map .right ≫ P.inr :=
        (d.pullback .right).w
      rw [e, r, ← Category.assoc]
      exact congrArg (· ≫ P.inr) (E₀.hom_ext _ _)

private theorem solve_least (E₀ : IsTerminal E) (f : X ⟶ P.sum (P.sum Y E) X)
    (s : X ⟶ P.sum Y E) (prefixed : Below (f ≫ P.desc (𝟙 _) s) s) :
    Below (solve E₀ f) s := by
  let D := decompose f
  apply below_on_cofan _ D.isColimit
  intro i
  cases i with
  | none =>
    change Below ((decompose f).residualIn ≫ solve E₀ f) (D.residualIn ≫ s)
    rw [solve_residual]
    exact below_failure E₀ _
  | some n =>
    change Below (D.finiteIn n ≫ solve E₀ f) (D.finiteIn n ≫ s)
    induction n with
    | zero =>
      suffices eq : D.finiteIn 0 ≫ solve E₀ f = D.finiteIn 0 ≫ (f ≫ P.desc (𝟙 _) s) by
        rw [eq]
        exact below_precomp _ prefixed
      change (decompose f).finiteIn 0 ≫ solve E₀ f = _
      rw [solve_finite, ← Category.assoc, D.zero_eq, Category.assoc, P.inl_desc, Category.comp_id]
      rfl
    | succ n ih =>
      have step (r : X ⟶ P.sum Y E) :
          D.finiteIn (n + 1) ≫ (f ≫ P.desc (𝟙 _) r) = D.advance n ≫ (D.finiteIn n ≫ r) := by
        rw [← Category.assoc, D.succ_eq, Category.assoc, Category.assoc, P.inr_desc]
      have unfold := congrArg (D.finiteIn (n + 1) ≫ ·) (solve_fixpoint E₀ f)
      rw [← unfold, step]
      have next := below_precomp (D.advance n) ih
      rw [← step s] at next
      exact below_trans next (below_precomp _ prefixed)

end PartialResults

section Codiagonal

variable {K : Type u} [Category.{v} K] (Q : Coproducts K)
  (iter : ∀ {A B : K}, (A ⟶ Q.sum B A) → (A ⟶ B))
  (relation : ∀ {A B : K}, (A ⟶ B) → (A ⟶ B) → Prop)
  (refl : ∀ {A B : K} (a : A ⟶ B), relation a a)
  (antisymm : ∀ {A B : K} {a b : A ⟶ B}, relation a b → relation b a → a = b)
  (fixpoint : ∀ {A B : K} (f : A ⟶ Q.sum B A), f ≫ Q.desc (𝟙 B) (iter f) = iter f)
  (naturality : ∀ {A B D : K} (f : A ⟶ Q.sum B A) (g : B ⟶ D),
    iter (f ≫ Q.map g (𝟙 A)) = iter f ≫ g)
  (least : ∀ {A B : K} (b : A ⟶ Q.sum B A) (s : A ⟶ B),
    relation (b ≫ Q.desc (𝟙 B) s) s → relation (iter b) s)

include refl antisymm fixpoint naturality least in
private theorem codiagonal_of_least {X Y : K} (b : X ⟶ Q.sum (Q.sum Y X) X) :
    iter (b ≫ Q.merge) = iter (iter b) := by
  let r := iter (b ≫ Q.merge)
  let q := iter (iter b)
  have flatten (s : X ⟶ Y) : Q.merge ≫ Q.desc (𝟙 Y) s = Q.desc (Q.desc (𝟙 Y) s) s := by
    simp [Coproducts.merge]
  apply antisymm
  · apply least
    have pre : (b ≫ Q.merge) ≫ Q.desc (𝟙 Y) q = q := calc
      _ = b ≫ Q.desc (Q.desc (𝟙 Y) q) q := by rw [Category.assoc, flatten]
      _ = (b ≫ Q.desc (𝟙 (Q.sum Y X)) (iter b)) ≫ Q.desc (𝟙 Y) q := by
        rw [Category.assoc, Q.desc_comp, Category.id_comp, fixpoint (iter b)]
      _ = q := by rw [fixpoint b, fixpoint (iter b)]
    change relation ((b ≫ Q.merge) ≫ Q.desc (𝟙 Y) q) q
    rw [pre]
    exact refl q
  · apply least
    rw [← naturality]
    apply least
    change relation ((b ≫ Q.map (Q.desc (𝟙 Y) r) (𝟙 X)) ≫ Q.desc (𝟙 Y) r) r
    have pre : (b ≫ Q.map (Q.desc (𝟙 Y) r) (𝟙 X)) ≫ Q.desc (𝟙 Y) r = r := by
      rw [Category.assoc, Q.map_desc, Category.comp_id, Category.id_comp, ← flatten,
        ← Category.assoc, fixpoint (b ≫ Q.merge)]
    rw [pre]
    exact refl r

end Codiagonal

variable {C : Type u} [Category.{v} C] [Hyperextensive C] {P : Coproducts C} {E : C}

theorem kleisli_codiagonal (E₀ : IsTerminal E) {X Y : Kleisli (monad P E)}
    (b : X ⟶ (P.kleisli (monad P E)).sum ((P.kleisli (monad P E)).sum Y X) X) :
    kleisliArrow (loop E₀ (b ≫ (P.kleisli (monad P E)).merge).of) =
      (kleisliArrow (loop E₀ (kleisliArrow (loop E₀ b.of)).of) : X ⟶ Y) := by
  let Q := P.kleisli (monad P E)
  let iter {A B : Kleisli (monad P E)} (f : A ⟶ Q.sum B A) : A ⟶ B :=
    kleisliArrow (loop E₀ f.of)
  let R {A B : Kleisli (monad P E)} (x y : A ⟶ B) : Prop := Below x.of y.of
  apply codiagonal_of_least Q (@iter) (@R) (fun a => below_refl a.of)
  · intro A B a b ab ba
    exact Kleisli.hom_ext (below_antisymm E₀ ab ba)
  · exact fun f => kleisli_fixpoint E₀ f
  · exact fun f g => kleisli_natural E₀ f g
  · intro A B f s h
    change Below ((f ≫ Q.desc (𝟙 B) s).of) s.of at h
    rw [expand_fixpoint] at h
    exact solve_least E₀ (f.of ≫ Exception.rearrange P E) s.of h

end Silmaril.Calco2019.Maybe.Proofs
