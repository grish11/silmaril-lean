module

public import Silmaril.Logic.Fragments.Defs
import Silmaril.Proofs.Logic.Fragments.Basic

@[expose] public section
namespace Silmaril.Logic.Fragments
universe u
variable {A B : Type u}

theorem all_map (f : A → B) (V : B → Prop) (xs : List A) :
    all V (xs.map f) ↔ all (V ∘ f) xs := Proofs.all_map f V xs
theorem any_map (f : A → B) (V : B → Prop) (xs : List A) :
    any V (xs.map f) ↔ any (V ∘ f) xs := Proofs.any_map f V xs
theorem positive_map_id (p : Positive A) : p.map id = p := Proofs.positive_id p
theorem positive_map_comp {C : Type u} (f : A → B) (g : B → C) (p : Positive A) :
    p.map (g ∘ f) = (p.map f).map g := Proofs.positive_comp f g p
theorem positive_satisfaction (f : A → B) (V : B → Prop) (p : Positive A) :
    (p.map f).eval V ↔ p.eval (V ∘ f) := Proofs.positive_sat f V p
theorem neg_map_id (p : ConjNeg A) : p.map id = p := Proofs.neg_id p
theorem neg_map_comp {C : Type u} (f : A → B) (g : B → C) (p : ConjNeg A) :
    p.map (g ∘ f) = (p.map f).map g := Proofs.neg_comp f g p
theorem neg_satisfaction (f : A → B) (V : B → Prop) (p : ConjNeg A) :
    (p.map f).eval V ↔ p.eval (V ∘ f) := Proofs.neg_sat f V p

def base : Fragment.{u} :=
  ⟨id, fun f => f, fun V => V, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => Iff.rfl⟩
def conjunctions : Fragment.{u} :=
  ⟨List, List.map, all, List.map_id, fun _ _ _ => (List.map_map ..).symm, all_map⟩
def disjunctions : Fragment.{u} :=
  ⟨List, List.map, any, List.map_id, fun _ _ _ => (List.map_map ..).symm, any_map⟩
def positive : Fragment.{u} :=
  ⟨Positive, Positive.map, Positive.eval, positive_map_id, positive_map_comp, positive_satisfaction⟩
def conjunctionNegation : Fragment.{u} :=
  ⟨ConjNeg, ConjNeg.map, ConjNeg.eval, neg_map_id, neg_map_comp, neg_satisfaction⟩

theorem positive_preservation {P Q : A → Prop} (h : ∀ a, P a → Q a) (p : Positive A) :
    p.eval P → p.eval Q := Proofs.positive_mono h p

theorem conjunction_satisfaction (V : A → Prop) (xs : List A) :
    (conjunction xs).eval V ↔ all V xs := Proofs.conjunction_sat V xs
theorem disjunction_satisfaction (V : A → Prop) (xs : List A) :
    (disjunction xs).eval V ↔ any V xs := Proofs.disjunction_sat V xs

/-- Classical De Morgan translation; the other fragment renaming results do
not need excluded middle beyond their base atomic satisfaction equivalence. -/
theorem demorgan_satisfaction (V : A → Prop) (p : Positive A) :
    p.toConjNeg.eval V ↔ p.eval V := Proofs.demorgan V p

theorem signed_preservation_iff (observed : Set A) (P Q : A → Prop) :
    PreservesSigned observed P Q ↔ Preserves observed P Q ∧ Reflects observed P Q :=
  Proofs.signed_iff observed P Q

theorem empty_conjunction (V : A → Prop) : all V [] := fun _ h => nomatch h
theorem empty_disjunction (V : A → Prop) : ¬ any V [] := fun ⟨_, h, _⟩ => nomatch h

/-- Adding truth is a positive simulation, but does not preserve negative atoms. -/
theorem positive_not_signed : Preserves (Set.univ : Set Unit) (fun _ => False) (fun _ => True) ∧
    ¬ PreservesSigned Set.univ (fun _ : Unit => False) (fun _ => True) :=
  ⟨fun _ _ h => h.elim, fun h => h ⟨false, ()⟩ (Set.mem_univ _) (fun h => h) trivial⟩

/-- No morphisms are lost when atomic truth was already reflected. -/
theorem no_reduction {P Q : A → Prop} {observed : Set A}
    (h : Preserves observed P Q) (reflect : Reflects observed P Q) :
    PreservesSigned observed P Q := (signed_preservation_iff observed P Q).mpr ⟨h, reflect⟩

theorem signed_map_id (xs : SignedConjunction A) : xs.map (Literal.map id) = xs := Proofs.signed_id xs
theorem signed_map_comp {C : Type u} (f : A → B) (g : B → C) (xs : SignedConjunction A) :
    xs.map (Literal.map (g ∘ f)) = (xs.map (Literal.map f)).map (Literal.map g) := Proofs.signed_comp f g xs
theorem signed_satisfaction (f : A → B) (V : B → Prop) (xs : SignedConjunction A) :
    all (Literal.eval V) (xs.map (Literal.map f)) ↔ all (Literal.eval (V ∘ f)) xs := Proofs.signed_sat f V xs

def signedConjunctions : Fragment.{u} :=
  ⟨SignedConjunction, fun f => List.map (Literal.map f), fun V => all (Literal.eval V),
    signed_map_id, signed_map_comp, signed_satisfaction⟩

theorem conjunction_natural (f : A → B) (xs : List A) :
    conjunction (xs.map f) = (conjunction xs).map f := Proofs.conjunction_natural f xs
theorem disjunction_natural (f : A → B) (xs : List A) :
    disjunction (xs.map f) = (disjunction xs).map f := Proofs.disjunction_natural f xs
theorem demorgan_natural (f : A → B) (p : Positive A) :
    (p.map f).toConjNeg = p.toConjNeg.map f := Proofs.demorgan_natural f p
theorem signed_natural (f : A → B) (xs : SignedConjunction A) :
    signedConjunction (xs.map (Literal.map f)) = (signedConjunction xs).map f := Proofs.signed_natural f xs
theorem signed_translation (V : A → Prop) (xs : SignedConjunction A) :
    (signedConjunction xs).eval V ↔ all (Literal.eval V) xs := Proofs.signed_translation V xs

def Translation.refl (F : Fragment.{u}) : Translation F F :=
  ⟨id, fun _ _ => rfl, fun _ _ => Iff.rfl⟩

def Translation.comp {F G H : Fragment.{u}} (t : Translation F G) (s : Translation G H) : Translation F H :=
  ⟨fun p => s.translate (t.translate p),
    fun f p => by rw [t.natural, s.natural],
    fun V p => (s.satisfaction V (t.translate p)).trans (t.satisfaction V p)⟩

def atomPositive : Translation base positive :=
  ⟨Positive.atom, fun _ _ => rfl, fun _ _ => Iff.rfl⟩
def conjunctionPositive : Translation conjunctions positive :=
  ⟨conjunction, conjunction_natural, conjunction_satisfaction⟩
def disjunctionPositive : Translation disjunctions positive :=
  ⟨disjunction, disjunction_natural, disjunction_satisfaction⟩
/-- Classically satisfaction preserving; the syntactic naturality is constructive. -/
def positiveNegation : Translation positive conjunctionNegation :=
  ⟨Positive.toConjNeg, demorgan_natural, demorgan_satisfaction⟩
def signedNegation : Translation signedConjunctions conjunctionNegation :=
  ⟨signedConjunction, signed_natural, signed_translation⟩

open CategoryTheory Silmaril.Logic.Institution

theorem lift_satisfaction (F : Fragment.{u}) {R S : Room.{u, u, u}} (c : R ⟶ S) (M : S.Mod) (p : F.Form R.Sen) :
    F.eval (S.Sat M) (F.map c.sen p) ↔ F.eval (R.Sat (c.mod.obj M)) p := Proofs.lift_sat F c M p

end Silmaril.Logic.Fragments
