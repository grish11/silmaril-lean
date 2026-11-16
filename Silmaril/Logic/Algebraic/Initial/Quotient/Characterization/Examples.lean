module

public import Silmaril.Logic.Algebraic.Initial.Quotient.Characterization.Thms
public import Silmaril.Logic.Algebraic.Initial.Quotient.Examples

@[expose] public section
namespace Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples
open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Institution.Examples

inductive Op : Nat → Type where
  | left : Op 0
  | right : Op 0

def signature : EQ.Signature := ⟨Unit, fun n _ _ => Op n⟩

def left : Ground signature () := .app (w := closedContext signature) .left (fun i => i.elim0)
def right : Ground signature () := .app (w := closedContext signature) .right (fun i => i.elim0)

def separating : EQ.Algebra signature where
  carrier _ := Bool
  op op _ := match op with
    | .left => false
    | .right => true

def singleton : EQ.Algebra signature where
  carrier _ := Unit
  op _ _ := ()

abbrev emptyTheory : Theory := emptyPresentation signature

def singletonModel : Models emptyTheory :=
  ⟨singleton, by intro e member; exact member.elim⟩

def separatingModel : Models emptyTheory :=
  ⟨separating, by intro e member; exact member.elim⟩

/-- Generatedness and all input equations alone permit a strictly extra quotient. -/
theorem singleton_generated : Generated singleton := by
  intro s x
  cases s
  cases x
  exact ⟨left, rfl⟩

theorem unrelated_constants : ¬ Rel emptyTheory (closedContext signature) left right := by
  intro relation
  have impossible : false = true := rel_sound separatingModel (fun i => i.elim0) relation
  cases impossible

theorem singleton_kernel_fails : ¬ ExactGroundKernel emptyTheory singleton := by
  intro kernel
  exact unrelated_constants ((kernel () left right).1 rfl)

theorem generated_model_not_initial : ¬ Nonempty (IsInitial singletonModel) := by
  intro initial
  exact singleton_kernel_fails ((initial_iff_generated_kernel singletonModel).1 initial).2

def identification : EQ.Equation signature :=
  ⟨0, closedContext signature, (), left, right⟩

def identifiedTheory : Theory := ⟨signature, {ULift.up identification}⟩

/-- An actual nonempty presentation, without assuming constructor no-confusion. -/
theorem identified_initial_properties :
    Generated (quotientModel identifiedTheory).obj ∧
      ExactGroundKernel identifiedTheory (quotientModel identifiedTheory).obj :=
  generated_kernel_of_initial _ (quotientModel_isInitial _)

theorem identified_constants_equal :
    evaluate (quotientModel identifiedTheory).obj left =
      evaluate (quotientModel identifiedTheory).obj right := by
  exact (quotientModel identifiedTheory).property (ULift.up identification)
    (Set.mem_singleton _) (fun i => i.elim0)

theorem identified_syntax_distinct : left ≠ right := by
  intro equality
  have impossible : false = true := congrArg (evaluate separating) equality
  cases impossible

namespace EmptySort

/-- Reuse the actual two-sort presentation whose equation declares an unused
variable of the empty lower sort. It must not become a closed equation. -/
abbrev theory := Presented.Examples.vacuousTheory

/-- The new characterization accepts the actual initial quotient while retaining
its empty sort and the distinct upper-sort constants. -/
theorem quotient_properties :
    Generated (quotientModel theory).obj ∧
      ExactGroundKernel theory (quotientModel theory).obj ∧
      IsEmpty ((quotientModel theory).obj.carrier false) := by
  obtain ⟨generated, kernel⟩ :=
    generated_kernel_of_initial (quotientModel theory) (quotientModel_isInitial theory)
  exact ⟨generated, kernel, Presented.Examples.lower_empty⟩

/-- A nonempty replacement for the lower carrier cannot be generated: evaluation
of a proposed closed term in the independent separating algebra gives Empty. -/
theorem singleton_not_generated : ¬ Generated Presented.Examples.singletonAlgebra := by
  intro generated
  obtain ⟨term, _⟩ := generated false ()
  have impossible := evaluate Presented.Examples.separating term
  change Empty at impossible
  exact impossible.elim

/-- The original vacuous equation is satisfied, but the genuine all-hom model
category rejects this nongenerated model as an initial object. -/
theorem singleton_not_initial : ¬ Nonempty (IsInitial Presented.Examples.singletonModel) := by
  intro initial
  exact singleton_not_generated
    ((initial_iff_generated_kernel Presented.Examples.singletonModel).1 initial).1

end EmptySort

end Silmaril.Logic.Algebraic.Initial.Presented.Characterization.Examples
