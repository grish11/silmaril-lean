module

public import Silmaril.Logic.Algebraic.Initial.Quotient.Thms

@[expose] public section
namespace Silmaril.Logic.Algebraic.Initial.Presented.Examples
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Institution.Structured

/-- The lower sort has no constructors; the upper sort has two constants. -/
inductive Op : (n : Nat) → (Fin n → Bool) → Bool → Type where
  | left : Op 0 (fun _ => true) true
  | right : Op 0 (fun _ => true) true

abbrev signature : EQ.Signature := ⟨Bool, Op⟩

def left {k : Nat} {Γ : Fin k → Bool} : EQ.Term signature Γ true :=
  .app .left (fun i => i.elim0)
def right {k : Nat} {Γ : Fin k → Bool} : EQ.Term signature Γ true :=
  .app .right (fun i => i.elim0)

/-- The same displayed equation has different meanings in these two contexts. -/
def closedEquation : EQ.Equation signature :=
  ⟨0, closedContext signature, true, left, right⟩
def vacuousEquation : EQ.Equation signature :=
  ⟨1, fun _ => false, true, left, right⟩

def collapseTheory : Theory := ⟨signature, {ULift.up closedEquation}⟩
def vacuousTheory : Theory := ⟨signature, {ULift.up vacuousEquation}⟩

/-- An independent separating model witnesses the empty-sort semantics. -/
def separating : EQ.Algebra signature where
  carrier s := if s then Bool else Empty
  op op _ := match op with
    | .left => false
    | .right => true

theorem separating_vacuous : vacuousEquation.Holds separating :=
  fun v => (v (⟨0, by decide⟩ : Fin 1)).elim

def separatingModel : Models vacuousTheory := ⟨separating, by
  intro e he
  have heq : e = ULift.up vacuousEquation := Set.mem_singleton_iff.mp he
  subst e
  exact separating_vacuous⟩

theorem raw_constants_distinct :
    (left : EQ.Term signature (closedContext signature) true) ≠ right := by
  intro h
  have impossible : false = true := congrArg
    (fun t => t.eval separating (fun i => i.elim0)) h
  cases impossible

/-- A nonempty equation theory genuinely identifies distinct syntax. -/
theorem equation_collapses :
    (projection collapseTheory (closedContext signature)).map true left =
      (projection collapseTheory (closedContext signature)).map true right := by
  apply Quotient.sound (s := setoid collapseTheory (closedContext signature) true)
  have h : Rel collapseTheory (closedContext signature)
      ((left : EQ.Term signature (closedContext signature) true).eval
        (closedAlgebra signature) (fun i => i.elim0))
      ((right : EQ.Term signature (closedContext signature) true).eval
        (closedAlgebra signature) (fun i => i.elim0)) :=
    Rel.equation (T := collapseTheory) (Γ := closedContext signature) closedEquation
      (Set.mem_singleton _) (fun (i : Fin 0) => i.elim0)
  exact (eval_closed_self (left : EQ.Term signature (closedContext signature) true)) ▸
    (eval_closed_self (right : EQ.Term signature (closedContext signature) true)) ▸ h

/-- The unused variable of the empty sort must not be dropped: this equation
has no complete closed instance, and its two constants remain distinct. -/
theorem vacuous_constants_distinct :
    (projection vacuousTheory (closedContext signature)).map true left ≠
      (projection vacuousTheory (closedContext signature)).map true right := by
  intro h
  have hs := rel_sound separatingModel (fun i => i.elim0) (Quotient.exact h)
  have impossible : false = true := hs
  cases impossible

/-- Quotienting does not manufacture a value in the empty lower sort. -/
theorem lower_empty : IsEmpty ((quotientModel vacuousTheory).obj.carrier false) :=
  ⟨fun q => ((foldHom separatingModel (fun i => i.elim0)).map false q).elim⟩

def arbitrary_axioms_initial : IsInitial (quotientModel collapseTheory) :=
  quotientModel_isInitial collapseTheory

theorem actual_constraint : Constraints.Sat equational (quotientModel collapseTheory).obj
    (initialConstraint collapseTheory) := quotientModel_satisfies collapseTheory

def singletonAlgebra : EQ.Algebra signature := ⟨fun _ => Unit, fun _ _ => ()⟩

def singletonModel : Models vacuousTheory :=
  ⟨singletonAlgebra, by
    intro e _ v
    exact @Subsingleton.elim Unit _ (e.down.lhs.eval singletonAlgebra v)
      (e.down.rhs.eval singletonAlgebra v)⟩

/-- Original model arrows are retained, including this noninjective map. -/
def collapseHom : separatingModel ⟶ singletonModel :=
  ⟨{ map := fun _ _ => (), map_op := fun _ _ => rfl }⟩

theorem collapse_not_injective : ¬ Function.Injective (collapseHom.hom.map true) := by
  intro hinj
  have he : collapseHom.hom.map true false = collapseHom.hom.map true true := rfl
  have impossible : false = true := hinj he
  cases impossible

/-- Old constructor models and new empty-theory quotients are genuinely isomorphic. -/
def empty_presentation_compatibility (A : EQ.Signature) :
    Initial.closedModel A ≅ quotientModel (emptyPresentation A) :=
  emptyPresentationIso A

end Silmaril.Logic.Algebraic.Initial.Presented.Examples
