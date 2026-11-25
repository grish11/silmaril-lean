module

public import Silmaril.Languages.Python.Core.Locals.Defs
public import Silmaril.Languages.Python.Core.Context.Thms
import Silmaril.Proofs.Languages.Python.Core.Locals.Properties

public section

namespace Silmaril.Languages.Python.Core.Locals

open Semantics.Operational

variable {slots : Nat} {source target : State slots} {label : Option (Event slots)}

theorem Store.write_here (store : Store slots) (slot : Fin slots) (value : Int) :
    store.write slot value slot = some value := by simp [Store.write]

theorem Store.write_other (store : Store slots) {slot index : Fin slots} (different : index ≠ slot)
    (value : Int) : store.write slot value index = store index := by simp [Store.write, different]

theorem Rhs.reduce_iff {store : Store slots} {rhs : Rhs slots} {next : Except (Error slots) (Rhs slots)} :
    rhs.reduce store = some next ↔ rhs.Step store next :=
  Proofs.Languages.Python.Core.Locals.reduce_iff

theorem State.advance_iff : source.advance = some (label, target) ↔ Step source label target :=
  Proofs.Languages.Python.Core.Locals.advance_iff

theorem Step.deterministic {other : State slots} {otherLabel : Option (Event slots)}
    (left : Step source label target) (right : Step source otherLabel other) :
    label = otherLabel ∧ target = other :=
  Proofs.Languages.Python.Core.Locals.deterministic left right

theorem progress (state : State slots) :
    (∃ label target, Step state label target) ∨ ∃ result, Observes state (.returned result) :=
  Proofs.Languages.Python.Core.Locals.progress state

theorem State.enter_answer (store : Store slots) (code : Code slots) :
    (enter store code).answer = code.eval store :=
  Proofs.Languages.Python.Core.Locals.enter_answer store code

theorem State.enter_budget (store : Store slots) (code : Code slots) :
    (enter store code).budget = code.budget :=
  Proofs.Languages.Python.Core.Locals.enter_budget store code

theorem Step.answer_eq (step : Step source label target) : source.answer = target.answer :=
  Proofs.Languages.Python.Core.Locals.answer_eq step

theorem Step.decreases (step : Step source label target) : target.budget < source.budget :=
  Proofs.Languages.Python.Core.Locals.decreases step

theorem noDiverges (state : State slots) : ¬ (ordinary slots).Diverges state :=
  Proofs.Languages.Python.Core.Locals.noDiverges state

theorem may_iff {outcome : Outcome (Result slots)} :
    (ordinary slots).May source outcome ↔ outcome = .returned source.answer.result :=
  Proofs.Languages.Python.Core.Locals.may_iff

theorem model_may_iff {code : Code slots} {outcome : Outcome (Result slots)} :
    (model slots).May code outcome ↔ outcome = .returned (code.eval (Store.empty slots)).result :=
  Proofs.Languages.Python.Core.Locals.model_may_iff

/-- A closed return in the frame has the original Core observation after tagging its exception. -/
theorem closed_may_iff (body : Core.Body) (admitted : Core.Profile.arithmetic.supports body.value)
    (result : Core.Completion) (slots : Nat) :
    (model slots).May (.ret (.arithmetic body.value)) (.returned (result.mapError .arithmetic)) ↔
      (Core.model .arithmetic).May body (.returned result) :=
  Proofs.Languages.Python.Core.Locals.closed_may_iff body admitted result slots

theorem State.pick_valid (state : State slots) : state.pick.Valid (model slots).semantics state :=
  Proofs.Languages.Python.Core.Locals.pick_valid state

theorem State.pick_known (state : State slots) : state.pick ≠ .stop .unknown :=
  Proofs.Languages.Python.Core.Locals.pick_known state

@[expose] def oracle (slots : Nat) : Oracle (model slots).semantics :=
  ⟨State.pick, State.pick_valid⟩

/-- Execute a lowered body in a new frame with all local slots unbound. -/
@[expose] def run (code : Code slots) (fuel : Nat) : Bounded (State slots) (Result slots) :=
  (oracle slots).run (State.enter (Store.empty slots) code) fuel

theorem run_sound (code : Code slots) (fuel : Nat) :
    (run code fuel).Sound (model slots).semantics (State.enter (Store.empty slots) code) fuel :=
  (oracle slots).run_sound _ _

theorem run_exact (state : State slots) {fuel : Nat} (enough : state.budget ≤ fuel) :
    (oracle slots).run state fuel =
      .stop (.finished state.answer.store state.answer.result) (.observed (.returned state.answer.result)) :=
  Proofs.Languages.Python.Core.Locals.run_exact (oracle slots) State.pick_known state enough

end Silmaril.Languages.Python.Core.Locals
