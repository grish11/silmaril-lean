module

public import Silmaril.Logic.Function.Defs

public section
namespace Silmaril.Logic.Function.Proofs
open CategoryTheory Silmaril.Semantics.Function
open Silmaril.Semantics.Region.Abstract (RuleMap)
universe u

theorem atom_id {A : Signature.{u}} (atom : Atom A) : Renaming.atom (𝟙 A) atom = atom := by
  cases atom with
  | node _ name => cases name <;> rfl
  | body => rfl
  | call _ edge => obtain ⟨⟨_, _, _⟩, _, name⟩ := edge; cases name <;> rfl

theorem atom_comp {A B C : Signature.{u}} (f : A ⟶ B) (g : B ⟶ C) (atom : Atom A) :
    Renaming.atom (f ≫ g) atom = g.atom (f.atom atom) := by
  cases atom with
  | node _ name => cases name <;> rfl
  | body => rfl
  | call _ edge => obtain ⟨⟨_, _, _⟩, _, name⟩ := edge; cases name <;> rfl

theorem ruleMap {A B : Signature.{u}} (f : A ⟶ B) : RuleMap f.atom (Laws A) (Laws B) := by
  intro rule present
  change PresenceRule rule at present
  cases present with
  | body context name row =>
    exact ⟨_, PresenceRule.body (f.context context) (f.internal name) (f.body row), rfl,
      Set.singleton_subset_iff.mpr ⟨_, rfl, rfl⟩⟩
  | caller context edge =>
    exact ⟨_, PresenceRule.caller (f.context context) (f.edge edge), rfl,
      Set.singleton_subset_iff.mpr ⟨_, rfl, rfl⟩⟩
  | callee context edge =>
    exact ⟨_, PresenceRule.callee (f.context context) (f.edge edge), rfl,
      Set.singleton_subset_iff.mpr ⟨_, rfl, rfl⟩⟩

end Silmaril.Logic.Function.Proofs
