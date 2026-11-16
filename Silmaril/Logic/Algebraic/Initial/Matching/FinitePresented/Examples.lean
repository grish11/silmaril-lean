module

public import Silmaril.Logic.Algebraic.Initial.Matching.FinitePresented.Thms

/-! A genuine equation identifies two distinct original nullary symbols. -/
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Matching
open Initial.Presented Initial.Presented.Characterization

abbrev constants : Profile := ⟨2, fun _ => 0⟩

def left : Ground constants.signature () := .app (w := fun _ : Fin 0 => ()) ⟨0, rfl⟩ (fun i => i.elim0)
def right : Ground constants.signature () := .app (w := fun _ : Fin 0 => ()) ⟨1, rfl⟩ (fun i => i.elim0)

def equation : EQ.Equation constants.signature :=
  ⟨0, closedContext constants.signature, (), left, right⟩

def equations : Set (Equations constants) := {ULift.up equation}

def separating : EQ.Algebra constants.signature where
  carrier _ := Fin 2
  op op _ := op.val

/-- Distinct syntax is identified by an actual original equation. -/
theorem syntax_distinct : left ≠ right := by
  intro h
  have opEqual : (0 : Fin 2) = 1 := congrArg (evaluate separating) h
  exact (by decide : (0 : Fin 2) ≠ 1) opEqual

theorem related : Rel (theory constants equations)
    (closedContext constants.signature) left right := by
  have h := Rel.equation (T := theory constants equations)
    (Γ := closedContext constants.signature) equation
    (by change (ULift.up equation : Equations constants) = ULift.up equation; rfl) (fun i => i.elim0)
  exact (eval_closed_self left) ▸ (eval_closed_self right) ▸ h

/-- The full generatedness-plus-spectrum compiler has a concrete native model
even though these two distinct constructor names are equal in its quotient. -/
theorem compiled_quotient :
    Satisfies
      (GuardedFOL.expand (SignedSpectrum.structureOf
        (quotientModel (theory constants equations)).obj))
      (compiled equations (𝟙 constants.signature)) :=
  quotient_expansion_satisfies equations

/-- The original positive equality is present, rather than a no-confusion clause. -/
theorem positive_present :
    FixedPoint.encodeFirstOrder (SignedSpectrum.positive (𝟙 constants.signature) left right) ∈
      compiled equations (𝟙 constants.signature) :=
  Or.inr ⟨_, SignedSpectrum.positive_mem _ related, rfl⟩

def collapse : constants.signature ⟶ constants.signature where
  sorts := id
  ops op := ⟨0, op.property⟩

theorem empty_unrelated :
    ¬ Rel (theory constants ∅) (closedContext constants.signature) left right := by
  intro h
  let M : Initial.Models (theory constants ∅) :=
    ⟨separating, by intro e he; exact he.elim⟩
  have equality := rel_sound M (fun i => i.elim0) h
  exact (by decide : (0 : Fin 2) ≠ 1) equality

/-- Recomputing the spectrum after this collision would lose its negative clause. -/
theorem collision_rejected (N : SignedSpectrum.NativeModel constants.signature) :
    ¬ Satisfies N (compiled (D := constants) ∅ collapse) := by
  intro h
  apply SignedSpectrum.collision_rejects (T := theory constants ∅) collapse empty_unrelated rfl N
  intro q hq
  exact (FixedPoint.firstOrder_satisfies N.base q).mp
    (h _ (Or.inr ⟨q, hq, rfl⟩))



/-- All-positive arities admit the genuinely empty algebra; no chosen default is used. -/
def emptyAlgebra (D : Profile) (positive : ∀ c, 0 < D.arity c) : EQ.Algebra D.signature where
  carrier _ := PEmpty
  op o args := args ⟨0, by simpa only [o.property] using positive o.val⟩

theorem ground_empty (D : Profile) (positive : ∀ c, 0 < D.arity c)
    (s : D.signature.S) : IsEmpty (Ground D.signature s) :=
  ⟨fun t => (evaluate (emptyAlgebra D positive) t).elim⟩

def emptyNative (D : Profile) (positive : ∀ c, 0 < D.arity c) :=
  GuardedFOL.expand (SignedSpectrum.structureOf (emptyAlgebra D positive))

/-- Padding has a raw inhabitant but contributes no active source-sort value. -/
theorem empty_active (D : Profile) (positive : ∀ c, 0 < D.arity c) :
    IsEmpty ((SignedSpectrum.decode (emptyNative D positive)).carrier ()) :=
  ⟨fun x => (GuardedFOL.activeEquiv
    (SignedSpectrum.structureOf (emptyAlgebra D positive)) () x).elim⟩

theorem raw_nonempty (D : Profile) (positive : ∀ c, 0 < D.arity c) :
    Nonempty ((emptyNative D positive).base.carrier (targetSort (𝟙 D.signature))) :=
  (emptyNative D positive).base.nonempty _

/-- Every original equation is vacuous in the empty generated algebra. Complete
contexts are retained, and no term is invented for an unused variable. -/
theorem empty_compiled (D : Profile) (positive : ∀ c, 0 < D.arity c)
    (E : Set (Equations D)) :
    Satisfies (emptyNative D positive) (compiled E (𝟙 D.signature)) := by
  apply (compiled_satisfaction E (𝟙 D.signature) _).mpr
  constructor
  · intro s x
    cases s
    exact ((empty_active D positive).false x).elim
  · intro s a b
    exact ((ground_empty D positive s).false a).elim

abbrev zeroOperations : Profile := ⟨0, fun c => c.elim0⟩

theorem zero_positive (c : Fin zeroOperations.count) : 0 < zeroOperations.arity c := c.elim0

theorem zero_operations_compiled :
    Satisfies (emptyNative zeroOperations zero_positive)
      (compiled (D := zeroOperations) ∅ (𝟙 zeroOperations.signature)) :=
  empty_compiled zeroOperations zero_positive ∅

abbrev unaryOnly : Profile := ⟨1, fun _ => 1⟩

theorem unary_positive (c : Fin unaryOnly.count) : 0 < unaryOnly.arity c := by
  change 0 < (1 : Nat)
  decide

/-- Variable 1 is declared but unused. Neither variable has a closed-term substitution. -/
def unaryEquation : EQ.Equation unaryOnly.signature :=
  ⟨2, (fun _ => ()), (), .var 0,
    .app (w := fun _ : Fin 1 => ()) ⟨0, rfl⟩ (fun _ => .var 0)⟩

def unaryEquations : Set (Equations unaryOnly) := {ULift.up unaryEquation}

theorem unary_no_complete_ground_instance :
    ¬ Nonempty (∀ i : Fin unaryEquation.k, Ground unaryOnly.signature (unaryEquation.ctx i)) := by
  rintro ⟨terms⟩
  exact (ground_empty unaryOnly unary_positive _).false (terms ⟨0, by decide⟩)

theorem unary_equation_compiled :
    Satisfies (emptyNative unaryOnly unary_positive)
      (compiled unaryEquations (𝟙 unaryOnly.signature)) :=
  empty_compiled unaryOnly unary_positive unaryEquations

theorem unary_active_empty :
    IsEmpty ((SignedSpectrum.decode (emptyNative unaryOnly unary_positive)).carrier ()) :=
  empty_active unaryOnly unary_positive


end Silmaril.Logic.Algebraic.Initial.Matching.FinitePresentedCompiler.Examples
