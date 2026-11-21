module

public import Silmaril.Semantics.Operational.Determinism.Fuel.Defs
public import Silmaril.Semantics.Operational.Determinism.Thms
import Silmaril.Proofs.Semantics.Operational.Determinism.Fuel

public section

namespace Silmaril.Semantics.Operational

variable {S O : Type*} {sem : WithUB S O}

theorem StepsN.reach {length : Nat} {source final : S} {step : S → S → Prop}
    (path : StepsN step length source final) : Relation.ReflTransGen step source final :=
  Proofs.Semantics.Operational.Determinism.unsized path

theorem Oracle.run_sound (oracle : Oracle sem) (source : S) (fuel : Nat) :
    (oracle.run source fuel).Sound sem source fuel :=
  Proofs.Semantics.Operational.Determinism.run_sound oracle source fuel

/-- A finite relational path is found with sufficient fuel when all reachable
decisions are known, the configured relation is deterministic, and observation
is terminal. No termination or decidability is assumed of arbitrary relations. -/
theorem Oracle.run_complete (oracle : Oracle sem) {start final : S} {length fuel : Nat} {outcome : Outcome O}
    (path : StepsN sem.step length start final) (observed : sem.observe final outcome) (enough : length ≤ fuel)
    (det : sem.toOpSem.DetFrom start) (discipline : sem.toOpSem.TerminalDiscipline)
    (safe : sem.SafeAt start) (known : ∀ ⦃source⦄, sem.toOpSem.Reach start source →
      oracle.pick source ≠ .stop .unknown) : oracle.run start fuel = .stop final (.observed outcome) :=
  Proofs.Semantics.Operational.Determinism.run_complete oracle path observed enough det discipline safe known

theorem Oracle.may_iff_run (oracle : Oracle sem) (start : S) (outcome : Outcome O)
    (det : sem.toOpSem.DetFrom start) (discipline : sem.toOpSem.TerminalDiscipline)
    (safe : sem.SafeAt start) (known : ∀ ⦃source⦄, sem.toOpSem.Reach start source →
      oracle.pick source ≠ .stop .unknown) :
    sem.toOpSem.May start outcome ↔ ∃ fuel final, oracle.run start fuel = .stop final (.observed outcome) :=
  Proofs.Semantics.Operational.Determinism.may_iff_run oracle start outcome det discipline safe known

theorem StepsN.no_diverges_of_normal {start final : S} {length : Nat} (path : StepsN sem.step length start final)
    (det : sem.toOpSem.DetFrom start) (normal : sem.toOpSem.Normal final) : ¬ sem.toOpSem.Diverges start :=
  Proofs.Semantics.Operational.Determinism.no_diverges_of_normal path det normal

theorem HasOpSem.may_of_run {Program : Type*} {model : HasOpSem Program S O}
    (oracle : Oracle model.semantics) {program : Program} {start final : S} {fuel : Nat} {outcome : Outcome O}
    (initial : model.initial program start) (run : oracle.run start fuel = .stop final (.observed outcome)) :
    model.May program outcome := by
  have evidence := oracle.run_sound start fuel
  rw [run] at evidence
  obtain ⟨_, _, path, observed⟩ := evidence
  exact ⟨start, initial, final, path.reach, observed⟩

end Silmaril.Semantics.Operational
