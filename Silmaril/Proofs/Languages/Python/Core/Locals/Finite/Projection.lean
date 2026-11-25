module

public import Silmaril.Languages.Python.Core.Locals.Finite.Defs
import Silmaril.Languages.Python.Core.Locals.Thms
import Silmaril.Semantics.Operational.Environment.Finite.Thms
import Silmaril.Semantics.Operational.Projection.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Locals.Finite

open Silmaril.Languages.Python.Core.Locals
open Silmaril.Languages.Python.Core.Locals.Finite
open Silmaril.Semantics.Operational

variable {slots : Nat}

theorem rowsOf_view (store : Store slots) : Environment.Finite.view (rowsOf store) = store :=
  Environment.Finite.view_encode (fun key _ _ => List.mem_finRange key)

theorem encode_view (state : State slots) : (Presentation.encode state).view = state := by
  cases state <;> simp [Presentation.encode, Presentation.view, rowsOf_view]

theorem enter_view (rows : Rows slots) (code : Code slots) :
    (Presentation.enter rows code).view = State.enter (Environment.Finite.view rows) code := by
  cases code <;> rfl

private theorem resume_view (rows : Rows slots) (cont : Continuation slots)
    (next : Except (Error slots) (Rhs slots)) :
    (Presentation.resume rows cont next).view = State.resume (Environment.Finite.view rows) cont next := by
  cases next <;> rfl

private theorem map_resume (rows : Rows slots) (cont : Continuation slots)
    (next : Option (Except (Error slots) (Rhs slots))) :
    (next.map fun result => (none, Presentation.resume rows cont result)).map
      (fun pair : Option (Event slots) × Presentation slots => (pair.1, pair.2.view)) =
    next.map (fun result => (none, State.resume (Environment.Finite.view rows) cont result)) := by
  cases next <;> simp [resume_view]

theorem advance_view (state : Presentation slots) :
    state.advance.map (fun pair => (pair.1, pair.2.view)) = state.view.advance := by
  cases state with
  | evaluating rows rhs cont =>
    cases rhs with
    | arithmetic expr =>
      cases expr with
      | int value =>
        cases cont with
        | ret => rfl
        | assign slot rest =>
          have projected : (Presentation.enter (rows.insert slot value) rest).view =
              State.enter (Store.write (Environment.Finite.view rows) slot value) rest := by
            rw [enter_view, Environment.Finite.view_insert]
            rfl
          exact congrArg (fun next => some (some (Event.write slot value), next)) projected
        | branch yes no =>
          exact congrArg (fun next => some (none, next))
            (enter_view rows (if value = 0 then no else yes))
      | binary op left right => exact map_resume rows cont _
    | read slot => exact map_resume rows cont ((Rhs.read slot).reduce (Environment.Finite.view rows))
    | binary op left right => exact map_resume rows cont _
    | logical op left right => exact map_resume rows cont _
  | raising rows error => rfl
  | finished rows result => rfl

theorem projection (slots : Nat) :
    Projection (presented slots) (semantic slots) Presentation.view id where
  sound {source action target} moved := by
    apply State.advance_iff.mp
    rw [← advance_view source]
    change source.advance = some (action, target) at moved
    rw [moved]
    rfl
  readback {source action target} step := by
    have advanced := State.advance_iff.mpr step
    rw [← advance_view source] at advanced
    cases found : source.advance with
    | none =>
      rw [found] at advanced
      cases advanced
    | some pair =>
      obtain ⟨label, next⟩ := pair
      rw [found] at advanced
      have eq : (label, next.view) = (action, target) := Option.some.inj advanced
      exact ⟨label, next, found, congrArg Prod.fst eq, congrArg Prod.snd eq⟩

theorem step_iff {source : Presentation slots} {action : Option (Event slots)} {target : State slots} :
    Step source.view action target ↔ ∃ next, source.advance = some (action, next) ∧ next.view = target := by
  rw [show Step source.view action target ↔ (semantic slots).Tr source.view action target from Iff.rfl,
    (projection slots).step_iff source action target]
  constructor
  · rintro ⟨label, next, moved, rfl, projected⟩
    exact ⟨next, moved, projected⟩
  · rintro ⟨next, moved, projected⟩
    exact ⟨action, next, moved, rfl, projected⟩

theorem execution_readback {source : Presentation slots} {actions : List (Option (Event slots))}
    {target : State slots} {states : List (State slots)}
    (run : (semantic slots).Execution source.view actions target states) :
    ∃ final witnesses, (presented slots).Execution source actions final witnesses ∧
      witnesses.map Presentation.view = states ∧ final.view = target := by
  obtain ⟨final, finiteActions, witnesses, trace, labels, stateList, last⟩ :=
    (projection slots).execution_readback run rfl
  simp only [List.map_id] at labels
  subst finiteActions
  exact ⟨final, witnesses, trace, stateList, last⟩

theorem terminal_iff {source : Presentation slots} {outcome : Outcome (Result slots)} :
    Observes source.view outcome ↔
      ∃ result, source.completion? = some result ∧ outcome = .returned result := by
  cases source with
  | evaluating rows rhs cont =>
    change Observes (.evaluating _ rhs cont) outcome ↔ _
    constructor
    · intro observed
      cases observed
    · rintro ⟨_, impossible, _⟩
      cases impossible
  | raising rows error =>
    change Observes (.raising _ error) outcome ↔ _
    constructor
    · intro observed
      cases observed
    · rintro ⟨_, impossible, _⟩
      cases impossible
  | finished rows result =>
    change Observes (.finished _ result) outcome ↔ _
    constructor
    · intro observed
      cases observed
      exact ⟨result, rfl, rfl⟩
    · rintro ⟨other, equal, rfl⟩
      cases equal
      exact .finished _ _

end Silmaril.Proofs.Languages.Python.Core.Locals.Finite
