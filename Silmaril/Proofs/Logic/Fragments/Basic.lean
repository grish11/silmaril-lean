module

public import Silmaril.Logic.Fragments.Defs

@[expose] public section
namespace Silmaril.Logic.Fragments.Proofs
universe u
variable {A B C : Type u}

theorem all_map (f : A → B) (V : B → Prop) (xs : List A) :
    all V (xs.map f) ↔ all (V ∘ f) xs := by simp [all]
theorem any_map (f : A → B) (V : B → Prop) (xs : List A) :
    any V (xs.map f) ↔ any (V ∘ f) xs := by simp [any]

theorem positive_id (p : Positive A) : p.map id = p := by
  induction p <;> simp_all [Positive.map]
theorem positive_comp (f : A → B) (g : B → C) (p : Positive A) :
    p.map (g ∘ f) = (p.map f).map g := by
  induction p <;> simp_all [Positive.map]
theorem positive_sat (f : A → B) (V : B → Prop) (p : Positive A) :
    (p.map f).eval V ↔ p.eval (V ∘ f) := by
  induction p <;> simp_all [Positive.map, Positive.eval]
theorem positive_mono {P Q : A → Prop} (h : ∀ a, P a → Q a) (p : Positive A) :
    p.eval P → p.eval Q := by
  induction p <;> simp_all [Positive.eval]; tauto

theorem neg_id (p : ConjNeg A) : p.map id = p := by
  induction p <;> simp_all [ConjNeg.map]
theorem neg_comp (f : A → B) (g : B → C) (p : ConjNeg A) :
    p.map (g ∘ f) = (p.map f).map g := by
  induction p <;> simp_all [ConjNeg.map]
theorem neg_sat (f : A → B) (V : B → Prop) (p : ConjNeg A) :
    (p.map f).eval V ↔ p.eval (V ∘ f) := by
  induction p <;> simp_all [ConjNeg.map, ConjNeg.eval]
theorem demorgan (V : A → Prop) (p : Positive A) : p.toConjNeg.eval V ↔ p.eval V := by
  classical
  induction p <;> simp_all [Positive.toConjNeg, Positive.eval, ConjNeg.eval, ConjNeg.disj]
  tauto

theorem conjunction_sat (V : A → Prop) (xs : List A) : (conjunction xs).eval V ↔ all V xs := by
  induction xs <;> simp_all [conjunction, Positive.eval, all]
theorem disjunction_sat (V : A → Prop) (xs : List A) : (disjunction xs).eval V ↔ any V xs := by
  induction xs <;> simp_all [disjunction, Positive.eval, any]

theorem literal_sat (f : A → B) (V : B → Prop) (l : Literal A) :
    (l.map f).eval V ↔ l.eval (V ∘ f) := by
  cases l with | mk sign a => cases sign <;> rfl

theorem signed_iff (observed : Set A) (P Q : A → Prop) :
    PreservesSigned observed P Q ↔ Preserves observed P Q ∧ Reflects observed P Q := by
  classical
  constructor
  · intro h
    refine ⟨fun a ha => h ⟨true, a⟩ ha, ?_⟩
    intro a ha hq
    by_contra hp
    exact h ⟨false, a⟩ ha hp hq
  · rintro ⟨forward, backward⟩ ⟨sign, a⟩ ha
    cases sign
    · exact fun hn hq => hn (backward a ha hq)
    · exact forward a ha

theorem signed_id (xs : SignedConjunction A) : xs.map (Literal.map id) = xs := by
  induction xs with
  | nil => rfl
  | cons l ls ih => cases l; simp [Literal.map, ih]
theorem signed_comp (f : A → B) (g : B → C) (xs : SignedConjunction A) :
    xs.map (Literal.map (g ∘ f)) = (xs.map (Literal.map f)).map (Literal.map g) := by
  induction xs with
  | nil => rfl
  | cons l ls ih => cases l; simp [Literal.map, ih]
theorem signed_sat (f : A → B) (V : B → Prop) (xs : SignedConjunction A) :
    all (Literal.eval V) (xs.map (Literal.map f)) ↔ all (Literal.eval (V ∘ f)) xs := by
  induction xs with
  | nil => simp [all]
  | cons l ls _ => simp [all, literal_sat]

theorem conjunction_natural (f : A → B) (xs : List A) :
    conjunction (xs.map f) = (conjunction xs).map f := by
  induction xs <;> simp_all [conjunction, Positive.map]

theorem disjunction_natural (f : A → B) (xs : List A) :
    disjunction (xs.map f) = (disjunction xs).map f := by
  induction xs <;> simp_all [disjunction, Positive.map]

theorem demorgan_natural (f : A → B) (p : Positive A) :
    (p.map f).toConjNeg = p.toConjNeg.map f := by
  induction p <;> simp_all [Positive.map, Positive.toConjNeg, ConjNeg.map, ConjNeg.disj]

theorem signed_natural (f : A → B) (xs : SignedConjunction A) :
    signedConjunction (xs.map (Literal.map f)) = (signedConjunction xs).map f := by
  induction xs with
  | nil => rfl
  | cons l ls ih =>
    cases l with | mk sign a => cases sign <;> simp [signedConjunction, Literal.map, Literal.toConjNeg, ConjNeg.map, ih]

theorem signed_translation (V : A → Prop) (xs : SignedConjunction A) :
    (signedConjunction xs).eval V ↔ all (Literal.eval V) xs := by
  induction xs with
  | nil => simp [signedConjunction, ConjNeg.eval, all]
  | cons l ls ih =>
    cases l with | mk sign a => cases sign <;> simp [signedConjunction, Literal.eval, Literal.toConjNeg, ConjNeg.eval, all, ih]

open CategoryTheory Silmaril.Logic.Institution

theorem lift_sat (F : Fragment.{u}) {R S : Room.{u, u, u}} (c : R ⟶ S) (M : S.Mod) (p : F.Form R.Sen) :
    F.eval (S.Sat M) (F.map c.sen p) ↔ F.eval (R.Sat (c.mod.obj M)) p := by
  rw [F.satisfaction]
  have eq : (S.Sat M) ∘ c.sen = R.Sat (c.mod.obj M) :=
    funext fun a => propext (c.sat M a)
  rw [eq]

end Silmaril.Logic.Fragments.Proofs
