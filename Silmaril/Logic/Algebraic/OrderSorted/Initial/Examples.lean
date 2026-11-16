module

public import Silmaril.Logic.Algebraic.OrderSorted.Initial.Thms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution.Examples

inductive Sorts where
  | lower | upper
  deriving DecidableEq
open Sorts

instance : PartialOrder Sorts where
  le s t := s = lower ∨ t = upper
  le_refl s := by cases s <;> simp
  le_trans := by intro s t u; cases s <;> cases t <;> cases u <;> simp_all
  le_antisymm := by intro s t; cases s <;> cases t <;> simp_all

theorem lower_upper : lower ≤ upper := Or.inl rfl

inductive Op : (n : ℕ) → (Fin n → Sorts) → Sorts → Type where
  | point : Op 0 Fin.elim0 lower
  | successor : Op 1 (fun _ => upper) upper

abbrev signature : Signature := ⟨⟨Sorts, Op⟩, inferInstance⟩

abbrev carrier : Sorts → Type
  | lower => Unit
  | upper => Nat

def inclusion {s t : Sorts} (h : s ≤ t) : carrier s → carrier t :=
  match s, t with
  | lower, lower => id
  | lower, upper => fun _ => 0
  | upper, upper => id
  | upper, lower => False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)

/-- A proper subsort: the lower singleton injects at zero into the upper naturals. -/
abbrev numeric : Model signature where
  algebra := {
    carrier := carrier
    op := fun o args => match o with
      | .base .point => ()
      | .base .successor => Nat.succ (args 0)
      | .inclusion _ _ h => inclusion h (args 0) }
  coherent := {
    identity := by intro s x; cases s <;> rfl
    injective := by
      intro s t h x y he
      cases s <;> cases t
      · exact he
      · exact Subsingleton.elim _ _
      · exact False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)
      · exact he
    composition := by
      intro s t u h j x
      cases s <;> cases t <;> cases u <;>
        first | rfl | exact False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction) }

theorem proper_coercion_image (x : numeric.algebra.carrier lower) :
    numeric.algebra.coerce lower_upper x ≠ (1 : Nat) := Nat.zero_ne_one

abbrev point : Free.Normal signature (Free.closedContext signature) lower :=
  Free.embed (.app .point (fun i => i.elim0))
abbrev widened : Free.Normal signature (Free.closedContext signature) upper := Free.coerce lower_upper point
abbrev successor : Free.Normal signature (Free.closedContext signature) upper :=
  Free.embed (.app .successor (fun _ => widened))

/-- The free model distinguishes a coerced constant from a new upper-sort value. -/
theorem distinct_free_values : widened ≠ successor := by
  intro h
  have he := congrArg (Free.eval numeric (fun i => i.elim0)) h
  change 0 = 1 at he
  exact Nat.zero_ne_one he

/-- Coercion paths are normalized while retaining their full principal core. -/
theorem free_path_coherence :
    Free.coerce (le_refl upper) (Free.coerce lower_upper point) =
      Free.coerce lower_upper point := Free.coerce_identity _

/-- This coherent algebra collapses all upper values; coherence alone is not initiality. -/
def collapsed : Model signature where
  algebra := {
    carrier _ := Unit
    op _ _ := () }
  coherent := {
    identity := fun _ _ => Subsingleton.elim _ _
    injective := fun _ _ _ _ => Subsingleton.elim _ _
    composition := fun _ _ _ => rfl }

/-- A genuine noninjective map is retained in the existing model category. -/
def numericCollapse : numeric ⟶ collapsed where
  map _ _ := ()
  map_op _ _ := rfl

theorem numericCollapse_not_injective : ¬ Function.Injective (numericCollapse.map upper) := by
  intro h
  exact Nat.zero_ne_one (h (a₁ := 0) (a₂ := 1) rfl)

/-- No homomorphism can preserve the upper successor from a singleton to Nat. -/
theorem no_collapsed_hom : IsEmpty (collapsed ⟶ numeric) := by
  refine ⟨fun f => ?_⟩
  have he := f.map_op (.base .successor) (fun _ => ())
  change f.map upper () = Nat.succ (f.map upper ()) at he
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) he

theorem collapsed_not_initial : ¬ Nonempty (IsInitial collapsed) := by
  rintro ⟨h⟩
  exact no_collapsed_hom.false (h.to numeric)

/-- A coherent but noninitial model also fails the actual shared initiality constraint. -/
theorem collapsed_fails_constraint :
    ¬ Silmaril.Logic.Institution.Structured.Constraints.Sat ordered collapsed
      (initialConstraint (emptyPresentation signature)) := by
  intro h
  let M : Models (emptyPresentation signature) :=
    Silmaril.Logic.Institution.Structured.SemanticModels.emptyModel ordered signature collapsed
  let N : Models (emptyPresentation signature) :=
    Silmaril.Logic.Institution.Structured.SemanticModels.emptyModel ordered signature numeric
  obtain ⟨hi⟩ := (initialConstraint_sat_iff _ M).1 h
  exact no_collapsed_hom.false (hi.to N).hom

/-- Only an upper constant: no generator or operation produces the lower sort. -/
inductive UpperOp : (n : ℕ) → (Fin n → Sorts) → Sorts → Type where
  | point : UpperOp 0 Fin.elim0 upper
abbrev upperSignature : Signature := ⟨⟨Sorts, UpperOp⟩, inferInstance⟩

abbrev upperCarrier : Sorts → Type
  | lower => Empty
  | upper => Unit

def upperInclusion {s t : Sorts} (h : s ≤ t) : upperCarrier s → upperCarrier t :=
  match s, t with
  | lower, _ => Empty.elim
  | upper, upper => id
  | upper, lower => False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)

abbrev upperOnly : Model upperSignature where
  algebra := {
    carrier := upperCarrier
    op := fun o args => match o with
      | .base .point => ()
      | .inclusion _ _ h => upperInclusion h (args 0) }
  coherent := {
    identity := by intro s x; cases s; exact x.elim; rfl
    injective := by
      intro s t h x y he
      cases s
      · exact x.elim
      · cases t
        · exact False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)
        · exact he
    composition := by
      intro s t u h j x
      cases s
      · exact x.elim
      · cases t
        · exact False.elim (by change upper = lower ∨ lower = upper at h; cases h <;> contradiction)
        · cases u
          · exact False.elim (by change upper = lower ∨ lower = upper at j; cases j <;> contradiction)
          · rfl }

/-- Initiality allows genuinely empty lower carriers. Evaluation into the
independent empty-lower model proves that the free lower carrier is empty. -/
theorem free_lower_empty : IsEmpty ((Free.closedModel upperSignature).algebra.carrier lower) :=
  ⟨fun t => Empty.elim ((Free.foldHom upperOnly (fun i => i.elim0)).map lower t)⟩

theorem free_upper_inhabited : Nonempty ((Free.closedModel upperSignature).algebra.carrier upper) :=
  ⟨Free.embed (.app .point (fun i => i.elim0))⟩

theorem upperOnly_free_initial : Nonempty (IsInitial (Free.closedModel upperSignature)) :=
  ⟨Free.closed_isInitial upperSignature⟩

theorem actual_initial_constraint :
    Silmaril.Logic.Institution.Structured.Constraints.Sat ordered (Free.closedModel upperSignature)
      (initialConstraint (emptyPresentation upperSignature)) := closedModel_satisfies upperSignature

end Silmaril.Logic.Algebraic.OrderSorted.Initial.Examples
