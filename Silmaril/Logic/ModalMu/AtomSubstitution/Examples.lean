module

public import Silmaril.Logic.ModalMu.AtomSubstitution.Thms
public import Silmaril.Logic.ModalMu.Reachability.Thms

@[expose] public section
namespace Silmaril.Logic.ModalMu.AtomSubstitution.Examples

abbrev source : Signature := ⟨Bool, Unit⟩
abbrev target : Signature := ⟨Unit, Bool⟩

/-- Only action true moves from the unlabelled entry to the labelled deadlock. -/
def chain : Model target where
  World := Bool
  point := false
  step a u v := a = true ∧ u = false ∧ v = true
  valuation _ := {w | w = true}

def replacement : Formula target 0 := reach true ()
def collapse (_ : Bool) : Formula target 0 := replacement
def move (_ : Unit) : Bool := true

theorem entry_replacement : Sat chain replacement := by
  apply (reach_iff chain true () false).mpr
  exact .next ⟨rfl, rfl, rfl⟩ (.here rfl)

/-- A closed inner μ keeps its own variable zero underneath the source ν. -/
theorem nested_binder_syntax :
    ((Formula.nu (.conj (.pos true) (.var 0)) : Formula source 0).replaceAtoms move collapse) =
      .nu (.conj (.mu (.disj (.pos ()) (.diamond true (.var 0)))) (.var 0)) := rfl

/-- The outer ν still denotes the inner replacement, rather than capturing its variable. -/
theorem nested_binder_truth :
    Sat chain ((Formula.nu (.conj (.pos true) (.var 0)) : Formula source 0).replaceAtoms
      move collapse) := by
  apply (sat_replaceAtoms (S := source) (T := target) move collapse chain _).mpr
  apply Formula.le_nu (atomReduct (S := source) (T := target) move collapse chain)
    (.conj (.pos true) (.var 0)) emptyEnv
    ((atomReduct (S := source) (T := target) move collapse chain).valuation true)
  · intro w hw
    exact ⟨hw, hw⟩
  · exact entry_replacement

/-- Negating the composite μ replacement excludes the entry which reaches the exit. -/
theorem negative_composite :
    ¬ Sat chain ((Formula.neg true : Formula source 0).replaceAtoms move collapse) := by
  rw [sat_replaceAtoms (S := source) (T := target)]
  exact fun h => h entry_replacement

/-- The explicit action map selects the actual moving action. -/
theorem mapped_action_reaches :
    Sat chain ((Formula.diamond () (.pos true) : Formula source 0).replaceAtoms
      move collapse) := by
  apply (sat_replaceAtoms (S := source) (T := target) move collapse chain _).mpr
  refine ⟨true, ⟨rfl, rfl, rfl⟩, ?_⟩
  exact (reach_iff chain true () true).mpr (.here rfl)

/-- Mapping the same source action to the dead action cannot take a step. -/
theorem dead_action_rejects :
    ¬ Sat chain ((Formula.diamond () (.pos true) : Formula source 0).replaceAtoms
      (fun _ => false) collapse) := by
  rw [sat_replaceAtoms (S := source) (T := target)]
  rintro ⟨v, hv, _⟩
  exact Bool.noConfusion hv.1

/-- Distinct source atoms may share a replacement; no injectivity is required. -/
theorem atom_collapse :
    Sat chain ((Formula.conj (.pos true) (.pos false) : Formula source 0).replaceAtoms
      move collapse) := by
  apply (sat_replaceAtoms (S := source) (T := target) move collapse chain _).mpr
  exact ⟨entry_replacement, entry_replacement⟩

/-- Atom replacement leaves an external fixed-point variable's valuation intact. -/
theorem open_variable_preserved :
    ((Formula.conj (.pos true) (.var 0) : Formula source 1).replaceAtoms
      move collapse).denote chain (fun _ => ∅) = ∅ := by
  ext w
  change (_ ∧ False) ↔ False
  simp only [and_false]

end Silmaril.Logic.ModalMu.AtomSubstitution.Examples
