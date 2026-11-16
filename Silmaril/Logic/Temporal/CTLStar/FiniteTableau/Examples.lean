module

public import Silmaril.Logic.Temporal.CTLStar.FiniteTableau.Thms
public import Silmaril.Logic.Temporal.CTLStar.Terminal.Examples

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.FiniteTableau.Examples
open LTL.Tableau Buchi.Automaton

def letter (_ : Nat) (_ : Unit) : Prop := True

theorem singleton_strongNext_rejects : ¬ Accepts (.strongNext (.top : NNF.Formula Unit)) 0 letter := by
  rw [accepts_iff]
  exact NNF.Formula.strongNext_at_last _ _ _

theorem singleton_weakNext_bottom_accepts : Accepts (.weakNext (.bot : NNF.Formula Unit)) 0 letter := by
  rw [accepts_iff]
  exact NNF.Formula.weakNext_at_last _ _ _

theorem singleton_postponed_until_rejects : ¬ Accepts (.until .top (.bot : NNF.Formula Unit)) 0 letter := by
  rw [accepts_iff, NNF.Formula.until_at_last]
  exact id

theorem singleton_release_without_left_accepts : Accepts (.release .bot (.top : NNF.Formula Unit)) 0 letter := by
  rw [accepts_iff, NNF.Formula.release_at_last]
  trivial

theorem singleton_release_requires_right : ¬ Accepts (.release .top (.bot : NNF.Formula Unit)) 0 letter := by
  rw [accepts_iff, NNF.Formula.release_at_last]
  exact id

/-- One actual finite word has a next letter, but no letter beyond its endpoint. -/
theorem one_edge_next_accepts : Accepts (.strongNext (.pos () : NNF.Formula Unit)) 1 letter := by
  rw [accepts_iff]
  exact ⟨Nat.le_refl 1, trivial⟩

theorem one_edge_two_next_rejects :
    ¬ Accepts (.strongNext (.strongNext (.top : NNF.Formula Unit))) 1 letter := by
  rw [accepts_iff]
  rintro ⟨_, h⟩
  exact NNF.Formula.strongNext_at_last letter .top 1 h

/-- All-true assignments cannot postpone an active Until past the final letter. -/
theorem terminal_guard_rejects_fake_until :
    ¬ (terminal (.until .top (.bot : NNF.Formula Unit)) (fun _ => true)).Holds (letter 0) := by
  simp [terminal, check, Guard.Holds, bit, left, right]

def distinct : NNF.Formula Bool := .conj (.pos true) (.neg false)

theorem distinct_leaves_accept : Accepts distinct 0 (fun _ a => a = true) := by
  rw [accepts_iff]
  exact ⟨rfl, Bool.noConfusion⟩

/-- Atom collapse preserves syntax correctly and turns this word constraint into a contradiction. -/
theorem collapsed_leaves_reject :
    ¬ Accepts (distinct.map (fun _ => ())) 0 letter := by
  rw [accepts_iff]
  exact fun h => h.2 h.1

/-- The finite language theorem is about the existing graph's actual path. -/
theorem actual_edge_next_atom :
    Accepts (.strongNext (.pos (.atom ())) : NNF.Formula (StateFormula Terminal.Examples.sig))
      1 (fun t a => a.Holds Terminal.Examples.edgeModel (Terminal.Examples.edgePath.state t)) := by
  apply (accepts_path_iff id Terminal.Examples.edgeModel Terminal.Examples.edgePath _ 1 rfl).mpr
  exact Terminal.Examples.edge_next_atom

end Silmaril.Logic.Temporal.CTLStar.FiniteTableau.Examples
