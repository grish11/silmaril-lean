module

public import Silmaril.Semantics.Calco2019.Maybe.Hyperextensive.Defs

public section

universe u v

namespace Silmaril.Calco2019.Maybe.Proofs

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Hyperextensive C]

private instance : Countable WalkingPair :=
  ⟨⟨fun j => match j with | .left => 0 | .right => 1,
    by intro j k h; cases j <;> cases k <;> simp_all⟩⟩

theorem hyperextensive_mono_left {A B X : C} {f : A ⟶ X} {g : B ⟶ X}
    (hc : IsColimit (BinaryCofan.mk f g)) : Mono f :=
  Hyperextensive.mono (C := C) (I := WalkingPair) (BinaryCofan.mk f g) hc .left

theorem hyperextensive_disjoint_binary {A B X : C} {f : A ⟶ X} {g : B ⟶ X}
    (hc : IsColimit (BinaryCofan.mk f g)) : Disjoint f g :=
  Hyperextensive.disjoint (C := C) (I := WalkingPair) (BinaryCofan.mk f g) hc
    (i := .left) (j := .right) (by decide)

omit [Hyperextensive C] in
private theorem disjoint_symm {A B X : C} {f : A ⟶ X} {g : B ⟶ X}
    (h : Disjoint f g) : Disjoint g f :=
  fun {_} p q pq => h q p pq.symm

theorem hyperextensive_pullback_binary {A B Z X : C} {l : A ⟶ Z} {r : B ⟶ Z}
    (hc : IsColimit (BinaryCofan.mk l r)) (f : X ⟶ Z) :
    Nonempty (PullbackCofan (I := WalkingPair) (BinaryCofan.mk l r) f) :=
  Hyperextensive.universal _ hc f

private def binary_colimit {A B Z X : C} {l : A ⟶ Z} {r : B ⟶ Z} {f : X ⟶ Z}
    (s : PullbackCofan (I := WalkingPair) (BinaryCofan.mk l r) f) :
    IsColimit (BinaryCofan.mk (s.incl .left) (s.incl .right)) := by
  let legs {Y : C} (l : s.obj .left ⟶ Y) (r : s.obj .right ⟶ Y) :
      ∀ i, s.obj i ⟶ Y := fun i => match i with | .left => l | .right => r
  refine BinaryCofan.isColimitMk
    (fun c => Cofan.IsColimit.desc s.colimit (legs c.inl c.inr)) ?_ ?_ ?_
  · intro c
    exact Cofan.IsColimit.fac s.colimit (legs c.inl c.inr) .left
  · intro c
    exact Cofan.IsColimit.fac s.colimit (legs c.inl c.inr) .right
  · intro c m ml mr
    apply Cofan.IsColimit.hom_ext s.colimit
    intro i
    cases i
    · exact ml.trans (Cofan.IsColimit.fac s.colimit (legs c.inl c.inr) .left).symm
    · exact mr.trans (Cofan.IsColimit.fac s.colimit (legs c.inl c.inr) .right).symm

omit [Hyperextensive C] in
@[reassoc (attr := simp)]
private theorem left_desc {A B X Y : C} {a : A ⟶ X} {b : B ⟶ X}
    (c : IsColimit (BinaryCofan.mk a b)) (f : A ⟶ Y) (g : B ⟶ Y) :
    a ≫ BinaryCofan.IsColimit.desc c f g = f :=
  BinaryCofan.IsColimit.inl_desc c f g

omit [Hyperextensive C] in
@[reassoc (attr := simp)]
private theorem right_desc {A B X Y : C} {a : A ⟶ X} {b : B ⟶ X}
    (c : IsColimit (BinaryCofan.mk a b)) (f : A ⟶ Y) (g : B ⟶ Y) :
    b ≫ BinaryCofan.IsColimit.desc c f g = g :=
  BinaryCofan.IsColimit.inr_desc c f g

private theorem factor_right {A B Z X : C} {l : A ⟶ Z} {r : B ⟶ Z}
    (hc : IsColimit (BinaryCofan.mk l r)) (f : X ⟶ Z) (hd : Disjoint f l) :
    ∃ g : X ⟶ B, g ≫ r = f := by
  obtain ⟨s⟩ := hyperextensive_pullback_binary hc f
  obtain ⟨empty⟩ := hd (s.incl .left) (s.map .left) (s.pullback .left).w
  let g := BinaryCofan.IsColimit.desc (binary_colimit s) (empty.to B) (s.map .right)
  refine ⟨g, ?_⟩
  apply (binary_colimit s).hom_ext
  rintro ⟨⟨⟩⟩
  · exact empty.hom_ext _ _
  · change s.incl .right ≫ g ≫ r = s.incl .right ≫ f
    exact (right_desc_assoc (binary_colimit s) (empty.to B) (s.map .right) r).trans
      (s.pullback .right).w.symm

omit [Hyperextensive C] in
private def complement_comp {A B X : C} (P : Coproducts C)
    {f : A ⟶ B} {g : B ⟶ X} (d : Complement f) (e : Complement g) :
    Complement (f ≫ g) where
  other := P.sum d.other e.other
  incl := P.desc (d.incl ≫ g) e.incl
  colimit := by
    refine BinaryCofan.isColimitMk
      (fun c => BinaryCofan.IsColimit.desc e.colimit (BinaryCofan.IsColimit.desc d.colimit c.inl (P.inl ≫ c.inr)) (P.inr ≫ c.inr)) ?_ ?_ ?_
    · intro c
      simp
    · intro c
      rw [P.desc_comp]
      apply P.hom_ext <;> simp
    · intro c m ml mr
      apply e.colimit.hom_ext
      rintro ⟨⟨⟩⟩
      · have h : g ≫ m = BinaryCofan.IsColimit.desc d.colimit c.inl (P.inl ≫ c.inr) := by
          apply d.colimit.hom_ext
          rintro ⟨⟨⟩⟩
          · change f ≫ g ≫ m = f ≫ BinaryCofan.IsColimit.desc d.colimit c.inl (P.inl ≫ c.inr)
            simp [← Category.assoc, ml]
          · change d.incl ≫ g ≫ m = d.incl ≫ BinaryCofan.IsColimit.desc d.colimit c.inl (P.inl ≫ c.inr)
            have h := congrArg ((P.inl (X := d.other) (Y := e.other)) ≫ ·) mr
            simpa [Category.assoc] using h
        exact h.trans (BinaryCofan.IsColimit.inl_desc _ _ _).symm
      · have h := congrArg ((P.inr (X := d.other) (Y := e.other)) ≫ ·) mr
        simpa [Category.assoc] using h


omit [Hyperextensive C] in
private theorem initial_of_coproduct {I : Type} {F : I → C} (c : Cofan F) (hc : IsColimit c)
    (hi : ∀ i, Nonempty (IsInitial (F i))) : Nonempty (IsInitial c.pt) := by
  classical
  let desc (Y : C) := Cofan.IsColimit.desc hc (fun i => (hi i).some.to Y)
  refine ⟨IsInitial.ofUniqueHom desc (fun Y g => ?_)⟩
  exact Cofan.IsColimit.hom_ext hc g (desc Y) (fun i => (hi i).some.hom_ext _ _)

private structure Included (X : C) where
  obj : C
  incl : obj ⟶ X
  complement : Complement incl

variable {P : Coproducts C} {Y X : C} {f : X ⟶ P.sum Y X}
  (first : PullbackCofan (I := WalkingPair) (BinaryCofan.mk P.inl P.inr) f)

private def onLeft : Included X :=
  ⟨first.obj .left, first.incl .left, ⟨first.obj .right, first.incl .right, binary_colimit first⟩⟩

private def onRight : Complement (first.incl .right) :=
  ⟨first.obj .left, first.incl .left, BinaryCofan.isColimitFlip (binary_colimit first)⟩

private noncomputable def preimage (d : Included X) :=
  (hyperextensive_pullback_binary d.complement.colimit (first.map .right)).some

private noncomputable def previous (d : Included X) : Included X :=
  let s := preimage first d
  ⟨s.obj .left, s.incl .left ≫ first.incl .right,
    complement_comp P ⟨s.obj .right, s.incl .right, binary_colimit s⟩ (onRight first)⟩

private noncomputable def finite : ℕ → Included X
  | 0 => onLeft first
  | n + 1 => previous first (finite n)

private noncomputable def advance (n : ℕ) : (finite first (n + 1)).obj ⟶ (finite first n).obj :=
  (preimage first (finite first n)).map .left

private theorem finite_succ_eq (n : ℕ) :
    (finite first (n + 1)).incl ≫ f = advance first n ≫ (finite first n).incl ≫ P.inr := by
  let s := preimage first (finite first n)
  change (s.incl .left ≫ first.incl .right) ≫ f =
    s.map .left ≫ (finite first n).incl ≫ P.inr
  rw [Category.assoc, (first.pullback .right).w, ← Category.assoc, (s.pullback .left).w,
    Category.assoc]
  rfl

private theorem finite_disjoint :
    Pairwise (fun n m : ℕ => Disjoint (finite first n).incl (finite first m).incl) := by
  intro n
  induction n with
  | zero =>
    intro m ne
    cases m with
    | zero => exact False.elim (ne rfl)
    | succ m =>
      intro D p q eq
      change p ≫ first.incl .left =
        q ≫ (preimage first (finite first m)).incl .left ≫ first.incl .right at eq
      exact hyperextensive_disjoint_binary (binary_colimit first) p (q ≫ (preimage first (finite first m)).incl .left)
        (eq.trans (Category.assoc _ _ _).symm)
  | succ n ih =>
    intro m ne
    cases m with
    | zero =>
      intro D p q eq
      change p ≫ (preimage first (finite first n)).incl .left ≫ first.incl .right =
        q ≫ first.incl .left at eq
      exact disjoint_symm (hyperextensive_disjoint_binary (binary_colimit first))
        (p ≫ (preimage first (finite first n)).incl .left) q ((Category.assoc _ _ _).trans eq)
    | succ m =>
      intro D p q eq
      let s := preimage first (finite first n)
      let t := preimage first (finite first m)
      let _ : Mono (first.incl .right) := hyperextensive_mono_left (onRight first).colimit
      change p ≫ s.incl .left ≫ first.incl .right = q ≫ t.incl .left ≫ first.incl .right at eq
      have equal : p ≫ s.incl .left = q ≫ t.incl .left :=
        (cancel_mono (first.incl .right)).mp ((Category.assoc _ _ _).trans (eq.trans (Category.assoc _ _ _).symm))
      apply ih (fun same => ne (congrArg Nat.succ same)) (p ≫ s.map .left) (q ≫ t.map .left)
      have sp : s.incl .left ≫ first.map .right = s.map .left ≫ (finite first n).incl :=
        (s.pullback .left).w
      have tp : t.incl .left ≫ first.map .right = t.map .left ≫ (finite first m).incl :=
        (t.pullback .left).w
      calc
        _ = (p ≫ s.incl .left) ≫ first.map .right :=
          (Category.assoc _ _ _).trans ((congrArg (p ≫ ·) sp.symm).trans (Category.assoc _ _ _).symm)
        _ = (q ≫ t.incl .left) ≫ first.map .right := congrArg (· ≫ first.map .right) equal
        _ = _ :=
          (Category.assoc _ _ _).trans ((congrArg (q ≫ ·) tp).trans (Category.assoc _ _ _).symm)

private theorem finite_sum_colimit {F : ℕ → C} :
    Nonempty (IsColimit (Cofan.mk (∐ F) (Sigma.ι F))) :=
  ⟨Cofan.IsColimit.mk _ (fun c => Sigma.desc c.inj)
    (fun c i => Sigma.ι_comp_desc c.inj i)
    (fun c _m h => Sigma.hom_ext _ _ (fun i => (h i).trans (Sigma.ι_comp_desc c.inj i).symm))⟩

private noncomputable def add_residual {F : ℕ → C} {X R : C} (f : ∀ n, F n ⟶ X) (r : R ⟶ X)
    (hc : IsColimit (BinaryCofan.mk (Sigma.desc f) r)) :
    IsColimit (Cofan.mk (f := fun j : Option ℕ => j.elim R F) X
      (fun j => match j with | some n => f n | none => r)) := by
  refine Cofan.IsColimit.mk _
    (fun c => BinaryCofan.IsColimit.desc hc (Sigma.desc fun n => c.inj (some n)) (c.inj none)) ?_ ?_
  · intro c i
    cases i with
    | none => exact right_desc hc _ _
    | some n =>
      change f n ≫ BinaryCofan.IsColimit.desc hc _ _ = _
      rw [← Sigma.ι_comp_desc f n, Category.assoc, left_desc hc, Sigma.ι_comp_desc]
  · intro c m h
    apply hc.hom_ext
    rintro ⟨⟨⟩⟩
    · change Sigma.desc f ≫ m = Sigma.desc f ≫ BinaryCofan.IsColimit.desc hc _ _
      rw [left_desc hc]
      apply Sigma.hom_ext
      intro n
      rw [Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_comp_desc]
      exact h (some n)
    · change r ≫ m = r ≫ BinaryCofan.IsColimit.desc hc _ _
      rw [right_desc hc]
      exact h none

set_option maxHeartbeats 450000 in
theorem hyperextensive_decompose (P : Coproducts C) {X Y : C} (f : X ⟶ P.sum Y X) :
    Nonempty (LoopDecomposition f) := by
  let first := (hyperextensive_pullback_binary (P.isColimit Y X) f).some
  let layers (n : ℕ) := (finite first n).obj
  let j (n : ℕ) : layers n ⟶ X := (finite first n).incl
  let u : ∐ layers ⟶ X := Sigma.desc j
  obtain ⟨residual⟩ : Nonempty (Complement u) :=
    Hyperextensive.union j (fun n => ⟨(finite first n).complement⟩) (finite_disjoint first)
  have residual_avoid (n : ℕ) : Disjoint residual.incl (j n) := by
    intro D p q eq
    apply disjoint_symm (hyperextensive_disjoint_binary residual.colimit) p (q ≫ Sigma.ι layers n)
    simpa only [Category.assoc, u, Sigma.ι_comp_desc] using eq
  have avoidFirst : Disjoint residual.incl (first.incl .left) := residual_avoid 0
  obtain ⟨r, hr⟩ := factor_right (binary_colimit first) residual.incl avoidFirst
  let next : residual.other ⟶ X := r ≫ first.map .right
  have avoidUnion : Disjoint next u := by
    intro D p q eq
    obtain ⟨colimit⟩ := finite_sum_colimit (F := layers)
    let s := (Hyperextensive.universal _ colimit q).some
    apply initial_of_coproduct _ s.colimit
    intro n
    let t := preimage first (finite first n)
    let a := s.incl n ≫ p ≫ r
    let b := s.map n
    have square : a ≫ first.map .right = b ≫ j n := by
      dsimp only [a, b, next] at *
      calc
        _ = s.incl n ≫ q ≫ u := by simpa only [Category.assoc] using congrArg (s.incl n ≫ ·) eq
        _ = _ := by
          rw [← Category.assoc, (s.pullback n).w, Category.assoc]
          simp [u]
    let toExit := (t.pullback .left).lift a b square
    have throughExit : toExit ≫ j (n + 1) = s.incl n ≫ p ≫ residual.incl := by
      change toExit ≫ t.incl .left ≫ first.incl .right = s.incl n ≫ p ≫ residual.incl
      rw [← Category.assoc]
      have ea : toExit ≫ t.incl .left = a := (t.pullback .left).lift_fst _ _ _
      rw [ea]
      change (s.incl n ≫ p ≫ r) ≫ first.incl .right = _
      simp only [Category.assoc, hr]
    exact residual_avoid (n + 1) (s.incl n ≫ p) toExit
      ((Category.assoc _ _ _).trans throughExit.symm)
  obtain ⟨stay, hstay⟩ := factor_right residual.colimit next avoidUnion
  refine ⟨{
    finite := layers
    residual := residual.other
    finiteIn := j
    residualIn := residual.incl
    result := first.map .left
    advance := advance first
    residualStep := stay
    zero_eq := (first.pullback .left).w
    succ_eq := finite_succ_eq first
    residual_eq := ?_
    isColimit := add_residual j residual.incl residual.colimit }⟩
  rw [← Category.assoc stay, hstay, ← hr, Category.assoc, (first.pullback .right).w]
  exact (Category.assoc _ _ _).symm

end Silmaril.Calco2019.Maybe.Proofs
