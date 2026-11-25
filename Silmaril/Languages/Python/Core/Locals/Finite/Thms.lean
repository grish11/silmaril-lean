module

public import Silmaril.Languages.Python.Core.Locals.Finite.Defs
import Silmaril.Proofs.Languages.Python.Core.Locals.Finite.Projection

public section

namespace Silmaril.Languages.Python.Core.Locals.Finite

open Semantics.Operational

variable {slots : Nat}

theorem rowsOf_view (store : Store slots) : Environment.Finite.view (rowsOf store) = store :=
  Proofs.Languages.Python.Core.Locals.Finite.rowsOf_view store

theorem Presentation.encode_view (state : State slots) : (encode state).view = state :=
  Proofs.Languages.Python.Core.Locals.Finite.encode_view state

theorem Presentation.enter_view (rows : Rows slots) (code : Code slots) :
    (enter rows code).view = State.enter (Environment.Finite.view rows) code :=
  Proofs.Languages.Python.Core.Locals.Finite.enter_view rows code

theorem entry (code : Code slots) : (model slots).initial code (Presentation.enter ∅ code).view :=
  (Presentation.enter_view ∅ code).trans rfl

theorem Presentation.advance_view (state : Presentation slots) :
    state.advance.map (fun pair => (pair.1, pair.2.view)) = state.view.advance :=
  Proofs.Languages.Python.Core.Locals.Finite.advance_view state

/-- State projection keeps the complete semantic successor, and action
projection is identity on the typed local events, including silent steps. -/
theorem projection (slots : Nat) :
    Projection (presented slots) (semantic slots) Presentation.view id :=
  Proofs.Languages.Python.Core.Locals.Finite.projection slots

theorem step_iff {source : Presentation slots} {action : Option (Event slots)} {target : State slots} :
    Step source.view action target ↔ ∃ next, source.advance = some (action, next) ∧ next.view = target :=
  Proofs.Languages.Python.Core.Locals.Finite.step_iff

theorem execution_readback {source : Presentation slots} {actions : List (Option (Event slots))}
    {target : State slots} {states : List (State slots)}
    (run : (semantic slots).Execution source.view actions target states) :
    ∃ final witnesses, (presented slots).Execution source actions final witnesses ∧
      witnesses.map Presentation.view = states ∧ final.view = target :=
  Proofs.Languages.Python.Core.Locals.Finite.execution_readback run

theorem terminal_iff {source : Presentation slots} {outcome : Outcome (Result slots)} :
    Observes source.view outcome ↔
      ∃ result, source.completion? = some result ∧ outcome = .returned result :=
  Proofs.Languages.Python.Core.Locals.Finite.terminal_iff

end Silmaril.Languages.Python.Core.Locals.Finite
