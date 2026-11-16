module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Logic.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFiniteLogic

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Metatheory
open Silmaril.Logic.SetTheory

universe u

/-- Actual rule packaging retains the existing finite institution exactly. -/
@[simp] theorem logic_toInst (n : ℕ) : (logic.{u} n).toInst = bundled.{u} n := rfl

/-- All actual bounded rules, including hypothesis leaves, are sound in actual finite models. -/
theorem logic_sound (n : ℕ) : (logic.{u} n).Sound :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFiniteLogic.logic_sound n

/-- The level inclusion's proof-carrying map projects to the existing institution inclusion. -/
theorem inclusionLogic_toInst {n m : ℕ} (h : n ≤ m) :
    (inclusionLogic.{u} h).toInstCoHom = inclusion.{u} h := rfl

/-- The existing Hets nodes are precisely the institutions of the actual bounded logics. -/
theorem hetsGraph_logic (n : ℕ) : hetsGraph.{u}.inst n = (logic.{u} n).toInst := rfl

/-- Every existing Hets inclusion edge has the actual bounded-rule logical transport. -/
theorem hetsGraph_inclusionLogic {n m : ℕ} (h : n ≤ m) :
    hetsGraph.{u}.comor (homOfLE h) = (inclusionLogic.{u} h).toInstCoHom := rfl

/-- The bounded institutional proof system has an actual Nat derivation at every rule budget. -/
theorem zero_derivable (n : ℕ) :
    (logic.{u} n).Derives (Discrete.mk ()) ∅ (zeroSentence n) := .zero .nil_ok

/-- An actual finite target model makes its full-rule bounded logical system consistent. -/
theorem logic_consistent (n : ℕ) [HasFiniteTower.{u} n] :
    ((logic.{u} n).er (Discrete.mk ())).Consistent ∅ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFiniteLogic.logic_consistent n

/-- Concrete consistency of the one-level bounded target logical system. -/
theorem logic_consistent_one : ((logic.{u + 1} 1).er (Discrete.mk ())).Consistent ∅ :=
  logic_consistent 1

/-- Concrete consistency of the two-level bounded target logical system. -/
theorem logic_consistent_two : ((logic.{u + 2} 2).er (Discrete.mk ())).Consistent ∅ :=
  logic_consistent 2

/-- Concrete consistency of the three-level bounded target logical system. -/
theorem logic_consistent_three : ((logic.{u + 3} 3).er (Discrete.mk ())).Consistent ∅ :=
  logic_consistent 3

/-- The compatibility inclusion projects to the same existing institution map. -/
@[simp] theorem inclusionLogical_toInstCoHom {n m : ℕ} (h : n ≤ m) :
    (inclusionLogical.{u} h).toInstCoHom = inclusion.{u} h := rfl

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite
