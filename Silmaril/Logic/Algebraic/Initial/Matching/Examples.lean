module

public import Silmaril.Logic.Algebraic.Initial.Matching.Institution
public import Mathlib.Tactic.FinCases

set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Initial.Matching.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

inductive NatOp : Nat → Type where
  | zero : NatOp 0
  | succ : NatOp 1

def natSignature : Signature := ⟨NatOp, .zero⟩
def natConstructors : Constructors := ⟨2, Fin.cases 0 (fun _ => 1), 0, rfl⟩
def natConstraint : Constraint natSignature :=
  ⟨natConstructors, Fin.cases .zero (fun _ => .succ)⟩
def naturals : EQ.Algebra natSignature.public where
  carrier _ := Nat
  op op args := match op with
    | .zero => 0
    | .succ => args 0 + 1

theorem naturals_generated : Generated natConstraint naturals := by
  intro n
  induction n with
  | zero => exact ⟨.node (0 : Fin 2) Fin.elim0, rfl⟩
  | succ n ih =>
    obtain ⟨t, rfl⟩ := ih
    exact ⟨.node (1 : Fin 2) (fun _ => t), rfl⟩

theorem naturals_noConfusion : NoConfusion natConstraint naturals := by
  constructor
  · intro c xs ys h
    fin_cases c
    · funext i; exact i.elim0
    · funext i
      fin_cases i
      exact Nat.succ.inj h
  · intro c d hcd xs ys h
    fin_cases c <;> fin_cases d
    · exact hcd rfl
    · exact Nat.noConfusion h
    · exact Nat.noConfusion h
    · exact hcd rfl

theorem naturals_actual : Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational
    naturals natConstraint.actual :=
  (actual_iff_fold_bijective _ _).2 ((bijective_iff_generated_noConfusion _ _).2
    ⟨naturals_generated, naturals_noConfusion⟩)

theorem naturals_native : (compile natConstraint).Satisfies (expand naturals).native := by
  apply (compile_actual_iff _ _).2
  rw [decode_expand]
  exact naturals_actual

/-- All constructors collapse in this actual algebra; generatedness alone holds. -/
def collapsed : EQ.Algebra natSignature.public where
  carrier _ := Unit
  op _ _ := ()

theorem collapsed_generated : Generated natConstraint collapsed := by
  intro x
  cases x
  exact ⟨.node (0 : Fin 2) Fin.elim0, rfl⟩
theorem collapsed_not_noConfusion : ¬ NoConfusion natConstraint collapsed := by
  intro h
  exact h.2 (0 : Fin 2) (1 : Fin 2) (by decide) Fin.elim0 (fun _ => ()) rfl

theorem collapsed_native_false : ¬ (compile natConstraint).Satisfies (expand collapsed).native := by
  intro h
  have hn := ((compile_satisfies_iff _ _).1 h).2
  rw [decode_expand] at hn
  exact collapsed_not_noConfusion hn

/-- Two disjoint successor chains: no confusion holds but the second chain is junk. -/
def junk : EQ.Algebra natSignature.public where
  carrier _ := Nat × Bool
  op op args := match op with
    | .zero => (0, false)
    | .succ => ((args 0).1 + 1, (args 0).2)

theorem junk_noConfusion : NoConfusion natConstraint junk := by
  constructor
  · intro c xs ys h
    fin_cases c
    · funext i; exact i.elim0
    · funext i
      fin_cases i
      have h1 : (xs (0 : Fin 1)).1 = (ys (0 : Fin 1)).1 :=
        Nat.succ.inj (congrArg (fun q : Nat × Bool => q.1) h)
      have h2 : (xs (0 : Fin 1)).2 = (ys (0 : Fin 1)).2 := by
        have hh := congrArg (fun q : Nat × Bool => q.2) h
        exact hh
      exact Prod.ext h1 h2
  · intro c d hcd xs ys h
    fin_cases c <;> fin_cases d
    · exact hcd rfl
    · exact Nat.noConfusion (congrArg Prod.fst h)
    · exact Nat.noConfusion (congrArg Prod.fst h)
    · exact hcd rfl

theorem junk_not_generated : ¬ Generated natConstraint junk := by
  have he : ∀ t, (Tree.eval natConstraint junk t).2 = false := by
    intro t
    induction t with
    | node c args ih =>
      fin_cases c
      · rfl
      · exact ih (0 : Fin 1)
  intro h
  obtain ⟨t, ht⟩ := h (0, true)
  have hf := he t
  rw [ht] at hf
  contradiction

theorem junk_native_false : ¬ (compile natConstraint).Satisfies (expand junk).native := by
  intro h
  have hg := ((compile_satisfies_iff _ _).1 h).1
  rw [decode_expand] at hg
  exact junk_not_generated hg

/-- Distinct original nullaries may collapse under a permitted ambient map. -/
def twoConstants : Constructors := ⟨2, fun _ => 0, 0, rfl⟩
inductive ConstantOp (α : Type) : Nat → Type where
  | symbol (value : α) : ConstantOp α 0

def twoSignature : Signature := ⟨ConstantOp Bool, .symbol false⟩
def singletonSignature : Signature := ⟨ConstantOp Unit, .symbol ()⟩
def collapseMap : twoSignature ⟶ singletonSignature where
  operations := fun op => match op with | .symbol _ => .symbol ()

def twoConstraint : Constraint twoSignature := ⟨twoConstants, fun c => .symbol (decide (c = (0 : Fin 2)))⟩
def singleton : EQ.Algebra singletonSignature.public where
  carrier _ := Unit
  op _ _ := ()

theorem translated_collapse_false : ¬ (compile (twoConstraint.map collapseMap)).Satisfies (expand singleton).native := by
  intro h
  have hn := ((compile_satisfies_iff _ _).1 h).2
  rw [decode_expand] at hn
  exact hn.2 (0 : Fin 2) (1 : Fin 2) (by decide) Fin.elim0 Fin.elim0 rfl

theorem collapseMap_not_injective : ¬ Function.Injective (@collapseMap.operations 0) := by
  intro h
  have he := h (a₁ := ConstantOp.symbol false) (a₂ := ConstantOp.symbol true) rfl
  cases he

theorem translated_actual_false : ¬ Silmaril.Logic.Institution.Structured.Constraints.Sat Initial.equational
    singleton (twoConstraint.map collapseMap).actual := by
  intro h
  apply translated_collapse_false
  apply (compile_actual_iff _ _).2
  rw [decode_expand]
  exact h

end Silmaril.Logic.Algebraic.Initial.Matching.Examples

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.actual_iff_fold_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.actual_iff_fold_bijective

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.generated_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.generated_denote

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.compile_actual_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.compile_actual_iff

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.toMatching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.toMatching

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.toMatching_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.toMatching_modelExpansive

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.entails_iff

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.satisfiable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.satisfiable_iff

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.unsatisfiable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.unsatisfiable_iff

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.Examples.naturals_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.Examples.naturals_native

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.Examples.collapsed_native_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.Examples.collapsed_native_false

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.Examples.junk_native_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.Examples.junk_native_false

/-- info: 'Silmaril.Logic.Algebraic.Initial.Matching.Examples.translated_collapse_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Logic.Algebraic.Initial.Matching.Examples.translated_collapse_false
