module

public import Silmaril.Logic.Algebraic.ManySorted.Horn
public import Silmaril.Logic.Algebraic.ManySorted.SingleSorted
public import Silmaril.Logic.Algebraic.ManySorted.Substitution

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted.Examples
open CategoryTheory

/-- Two syntactically distinct sorts and two nullary symbols at every sort. -/
def twoSorted : Signature Bool := ⟨fun _ _ _ => Bool⟩
def separated : Model twoSorted := ⟨fun _ => Bool, fun op _ => op⟩
def collapsed : Model twoSorted := ⟨fun _ => Bool, fun _ _ => false⟩
def closedEquation : Equation twoSorted :=
  ⟨0, Fin.elim0, false, .app (inputs := Fin.elim0) false (fun i => nomatch i), .app (inputs := Fin.elim0) true (fun i => nomatch i)⟩

theorem collapsed_satisfies : Equation.Satisfies collapsed closedEquation := fun _ => rfl

theorem separated_refutes : ¬ Equation.Satisfies separated closedEquation := by
  intro valid
  exact Bool.false_ne_true (valid (fun i => nomatch i))

/-- Nonidentity renaming exchanges the two operation symbols. -/
def exchange : twoSorted ⟶ twoSorted := ⟨fun op => !op⟩

theorem reduct_changes_operation :
    (Signature.Hom.reduct exchange separated).operation
      (n := 0) (inputs := Fin.elim0) (output := false) false Fin.elim0 = true := rfl

/-- Ordinary single-sorted symbols for a toy no-op elimination pass. -/
inductive Instruction : Nat → Type where
  | zero : Instruction 0
  | nop : Instruction 1

def instructionSignature := SingleSorted.ofArity Instruction

def execution : Model instructionSignature where
  carrier _ := Nat
  operation op args := match op with
    | .zero => 0
    | .nop => args 0

def removeNop : Equation instructionSignature :=
  ⟨1, fun _ => PUnit.unit, PUnit.unit,
    .app Instruction.nop (fun _ => .var 0), .var 0⟩

/-- A toy peephole law, valid for every state; substitutions can insert any term. -/
theorem removeNop_correct : Equation.Satisfies execution removeNop := fun _ => rfl

/-- Equational Horn congruence with a satisfiable premise, not a false antecedent. -/
def nopCongruence : Horn instructionSignature :=
  ⟨2, fun _ => PUnit.unit,
    [⟨PUnit.unit, .var 0, .var 1⟩],
    ⟨PUnit.unit, .app Instruction.nop (fun _ => .var 0),
      .app Instruction.nop (fun _ => .var 1)⟩⟩

theorem nopCongruence_correct : Horn.Satisfies execution nopCongruence := by
  unfold Horn.Satisfies nopCongruence
  dsimp only
  intro v premises
  have h := premises ⟨PUnit.unit, .var 0, .var 1⟩ (List.mem_cons_self ..)
  exact h

theorem nopCongruence_premise_satisfiable :
    ∃ v : Fin 2 → Nat, v 0 = v 1 := ⟨fun _ => 0, rfl⟩
end Silmaril.Logic.Algebraic.ManySorted.Examples

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted.Examples

/-- The toy pass contract as an actual shared axiom presentation. -/
def nopSpecification : Presentation PUnit :=
  ⟨instructionSignature, {removeNop}⟩

theorem execution_models_nopSpecification :
    ∀ e ∈ nopSpecification.axioms, Equation.Satisfies execution e := by
  intro e membership
  have same : e = removeNop := membership
  subst e
  exact removeNop_correct
end Silmaril.Logic.Algebraic.ManySorted.Examples
