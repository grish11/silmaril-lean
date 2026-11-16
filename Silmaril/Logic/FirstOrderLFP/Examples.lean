module

public import Silmaril.Logic.FirstOrderLFP

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP.Examples
open Reachability Silmaril.Logic.Institution.Examples

/-- An infinite carrier: reaching any natural from zero needs only a finite path. -/
theorem natural_chain (n : Nat) :
    ![0, n] ∈ reaches.denote (model Nat (fun a b => b = a + 1))
      (noRelations (fun a b : Nat => b = a + 1)) := by
  apply (reaches_finite_path _ _).mpr
  induction n with
  | zero => exact .refl
  | succ n ih => exact ih.tail rfl

/-- Reversing the chain does not invent a path. -/
theorem chain_nonreach :
    ![1, 0] ∉ reaches.denote (model Nat (fun a b => b = a + 1))
      (noRelations (fun a b : Nat => b = a + 1)) := by
  intro h
  have hp : Relation.ReflTransGen (fun a b : Nat => b = a + 1) 1 0 :=
    (reaches_finite_path _ _).mp h
  have hle : ∀ {a b : Nat}, Relation.ReflTransGen (fun a b => b = a + 1) a b → a ≤ b := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | @tail b c hab hbc ih => exact hbc ▸ Nat.le_succ_of_le ih
  exact Nat.not_succ_le_zero 0 (hle hp)

def cycleEdge (a b : Fin 3) : Prop := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)

/-- The two-state cycle is real, but the third state stays unreachable. -/
theorem cycle_path :
    ![0, 0] ∈ lfpSet (model (Fin 3) cycleEdge) (Γ := context 0) binaryBody
      (noRelations cycleEdge) (noObjects cycleEdge) := by
  apply (binary_finite_path cycleEdge _).mpr
  exact (Relation.TransGen.single (show cycleEdge 0 1 from Or.inl ⟨rfl, rfl⟩)).tail
    (show cycleEdge 1 0 from Or.inr ⟨rfl, rfl⟩)

theorem cycle_nonreach :
    ![0, 2] ∉ reaches.denote (model (Fin 3) cycleEdge) (noRelations cycleEdge) := by
  intro h
  have hp : Relation.ReflTransGen cycleEdge 0 2 := (reaches_finite_path _ _).mp h
  have stays : ∀ {b : Fin 3}, Relation.ReflTransGen cycleEdge 0 b → b = 0 ∨ b = 1 := by
    intro b hb
    induction hb with
    | refl => exact Or.inl rfl
    | tail _ hedge _ => exact hedge.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  rcases stays hp with h0 | h1
  · exact (by decide : (2 : Fin 3) ≠ 0) h0
  · exact (by decide : (2 : Fin 3) ≠ 1) h1

/-- Changing only the captured target changes the formula's truth value. -/
theorem parameter_matters :
    ![0, 0] ∈ reaches.denote (model (Fin 3) cycleEdge) (noRelations cycleEdge) ∧
    ![0, 2] ∉ reaches.denote (model (Fin 3) cycleEdge) (noRelations cycleEdge) :=
  ⟨(reaches_finite_path _ _).mpr .refl, cycle_nonreach⟩

/-- Empty carriers follow the pinned public FOL policy. -/
theorem empty_universal :
    (fun i => i.elim0) ∈
      (Formula.all (Δ := context 1) (.base .tt) : Formula signature emptyProfiles (context 0)).denote
        (model Empty (fun _ _ => False)) (noRelations (fun _ _ : Empty => False)) :=
  fun x => x.elim

theorem empty_existential :
    (fun i => i.elim0) ∉
      (Formula.ex (Δ := context 1) (.base .tt) : Formula signature emptyProfiles (context 0)).denote
        (model Empty (fun _ _ => False)) (noRelations (fun _ _ : Empty => False)) :=
  fun ⟨x, _⟩ => x.elim

/-- info: 'Silmaril.Logic.FirstOrderLFP.Formula.denote_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Formula.denote_map
/-- info: 'Silmaril.Logic.FirstOrderLFP.Reachability.binary_finite_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binary_finite_path
/-- info: 'Silmaril.Logic.FirstOrderLFP.Reachability.parameter_finite_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parameter_finite_path
/-- info: 'Silmaril.Logic.FirstOrderLFP.Reachability.transitive_finite_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transitive_finite_path
/-- info: 'Silmaril.Logic.FirstOrderLFP.fol_sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fol_sat_iff
/-- info: 'Silmaril.Logic.FirstOrderLFP.fol_unsat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fol_unsat_iff
/-- info: 'Silmaril.Logic.FirstOrderLFP.fol_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fol_entails_iff

end Silmaril.Logic.FirstOrderLFP.Examples
