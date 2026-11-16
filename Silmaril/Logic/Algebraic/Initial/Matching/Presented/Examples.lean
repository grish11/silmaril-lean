module

public import Silmaril.Logic.Algebraic.Initial.Matching.Presented.Thms

/-! A genuine equation identifies two distinct original nullary symbols. -/
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.PresentedCompiler.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Initial.Presented Initial.Presented.Characterization

abbrev constants : Constructors := ⟨2, fun _ => 0, 0, rfl⟩

def left : Ground constants.signature.public () := .app (w := fun _ : Fin 0 => ()) ⟨0, rfl⟩ (fun i => i.elim0)
def right : Ground constants.signature.public () := .app (w := fun _ : Fin 0 => ()) ⟨1, rfl⟩ (fun i => i.elim0)

def equation : EQ.Equation constants.signature.public :=
  ⟨0, closedContext constants.signature.public, (), left, right⟩

def equations : Set (Equations constants) := {ULift.up equation}

def separating : EQ.Algebra constants.signature.public where
  carrier _ := Fin 2
  op op _ := op.val

/-- Distinct syntax is identified by an actual original equation. -/
theorem syntax_distinct : left ≠ right := by
  intro h
  have opEqual : (0 : Fin 2) = 1 := congrArg (evaluate separating) h
  exact (by decide : (0 : Fin 2) ≠ 1) opEqual

theorem related : Rel (theory constants equations)
    (closedContext constants.signature.public) left right := by
  have h := Rel.equation (T := theory constants equations)
    (Γ := closedContext constants.signature.public) equation
    (by change (ULift.up equation : Equations constants) = ULift.up equation; rfl) (fun i => i.elim0)
  exact (eval_closed_self left) ▸ (eval_closed_self right) ▸ h

/-- The full generatedness-plus-spectrum compiler has a concrete native model
even though these two distinct constructor names are equal in its quotient. -/
theorem compiled_quotient :
    Satisfies
      (GuardedFOL.expand (SignedSpectrum.structureOf
        (quotientModel (theory constants equations)).obj))
      (compiled equations (𝟙 constants.signature.public)) :=
  quotient_expansion_satisfies equations

/-- The original positive equality is present, rather than a no-confusion clause. -/
theorem positive_present :
    FixedPoint.encodeFirstOrder (SignedSpectrum.positive (𝟙 constants.signature.public) left right) ∈
      compiled equations (𝟙 constants.signature.public) :=
  Or.inr ⟨_, SignedSpectrum.positive_mem _ related, rfl⟩

def collapse : constants.signature.public ⟶ constants.signature.public where
  sorts := id
  ops op := ⟨0, op.property⟩

theorem empty_unrelated :
    ¬ Rel (theory constants ∅) (closedContext constants.signature.public) left right := by
  intro h
  let M : Initial.Models (theory constants ∅) :=
    ⟨separating, by intro e he; exact he.elim⟩
  have equality := rel_sound M (fun i => i.elim0) h
  exact (by decide : (0 : Fin 2) ≠ 1) equality

/-- Recomputing the spectrum after this collision would lose its negative clause. -/
theorem collision_rejected (N : SignedSpectrum.NativeModel constants.signature.public) :
    ¬ Satisfies N (compiled (D := constants) ∅ collapse) := by
  intro h
  apply SignedSpectrum.collision_rejects (T := theory constants ∅) collapse empty_unrelated rfl N
  intro q hq
  exact (FixedPoint.firstOrder_satisfies N.base q).mp
    (h _ (Or.inr ⟨q, hq, rfl⟩))

/-- The reused selected-nullary profile forces the retained active sort inhabited.
Empty active ambient sorts outside that image remain permitted. -/
theorem retained_active_nonempty {D : Constructors} {B : EQ.Signature}
    (σ : D.signature.public ⟶ B) (N : SignedSpectrum.NativeModel B) :
    Nonempty ((reduct σ N).carrier ()) :=
  ⟨(reduct σ N).op (w := fun _ => ()) (s := ()) D.signature.constant
    (fun i => i.elim0)⟩

end Silmaril.Logic.Algebraic.Initial.Matching.PresentedCompiler.Examples
