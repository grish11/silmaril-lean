module

public import Silmaril.Logic.Modal.Propositional

@[expose] public section

namespace Silmaril.Logic.Modal.Examples

/-- Two control-flow states: the entry points to the exit; the exit deadlocks. -/
def stepModel : Model ⟨Unit⟩ where
  World := Bool
  accessible w v := w = false ∧ v = true
  valuation _ w := w = true
  point := false

/-- Every immediate successor of entry is an exit state. -/
theorem entry_box_exit : Sat stepModel (.box (.atom ())) := by
  intro v hv
  exact hv.2

/-- Entry itself is not exit. -/
theorem entry_not_exit : ¬ Sat stepModel (.atom ()) := Bool.false_ne_true

/-- T is not valid on arbitrary K frames. -/
theorem T_countermodel : ¬ Sat stepModel (.imp (.box (.atom ())) (.atom ())) := by
  intro h
  exact entry_not_exit (h entry_box_exit)

/-- Vacuous box truth at a deadlocked state is intentional Kripke semantics. -/
theorem deadlock_box_bottom : (Formula.box (.bot : Formula ⟨Unit⟩)).Holds stepModel true := by
  intro v hv
  exact Bool.noConfusion hv.1

end Silmaril.Logic.Modal.Examples
