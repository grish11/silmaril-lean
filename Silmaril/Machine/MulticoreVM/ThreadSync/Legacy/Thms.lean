module

public import Silmaril.Machine.MulticoreVM.ThreadSync.Legacy.Defs
public import Silmaril.Machine.MulticoreVM.Thms
import Silmaril.Proofs.Machine.MulticoreVM.ThreadSync.Legacy

public section

namespace Silmaril.Machine.MulticoreVM.ThreadSync.Legacy

open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {Thread Key Value Local Output : Type u}
variable [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value]

/-- On schedules of lifted local actions, the synchronization VM gives the embedded
legacy result, including rejection of the same unsuccessful schedules. -/
theorem execute_lift (localExec : LocalExec Thread Local Output) (words : Key → Value)
    (schedule : Schedule Thread PUnit) (store : Store Thread Local) :
    execute (ThreadSync.exec (liftProgram localExec)) (liftSchedule schedule) (liftStore words store) =
      (execute (exec localExec) schedule store).map (liftOutcome words) :=
  Proofs.Machine.MulticoreVM.ThreadSync.Legacy.execute_lift localExec words schedule store

/-- The same scheduled-run correspondence as a relation on named words and full stores.
The shared word map is arbitrary and is preserved throughout the lifted execution. -/
theorem scheduled_lift_iff (localExec : LocalExec Thread Local Output) (words : Key → Value)
    (schedule : Schedule Thread PUnit) {initial final : Store Thread Local} {word : Word Thread Output} :
    Scheduled (ThreadSync.step (liftProgram localExec)) (liftSchedule schedule) (liftStore words initial)
      (liftWord word) (liftStore words final) ↔
    Scheduled (ofExecutor (exec localExec)) schedule initial word final :=
  Proofs.Machine.MulticoreVM.ThreadSync.Legacy.scheduled_lift_iff localExec words schedule

/-- The local callback extracted from Toy agrees with the existing whole-store executor
when the decision supplies no child ID. Spawn has no step under such a decision. -/
theorem toy_exec_eq (thread : Toy.ThreadId) (cfg : Toy.Config) :
    Toy.exec thread none cfg = exec toyLocal thread ⟨⟩ cfg :=
  Proofs.Machine.MulticoreVM.ThreadSync.Legacy.toy_exec_eq thread cfg

/-- For the same Toy thread schedule with no child choices, compare the synchronization
VM directly to the existing Toy executor. Every successful step is an add or emit. -/
theorem execute_toy {K V : Type} [DecidableEq K] [DecidableEq V]
    (words : K → V) (schedule : Schedule Toy.ThreadId PUnit) (initial : Toy.Config) :
    execute (ThreadSync.exec (liftProgram toyLocal)) (liftSchedule schedule) (liftStore words initial) =
      (execute Toy.exec (toySchedule schedule) initial).map (liftOutcome words) :=
  Proofs.Machine.MulticoreVM.ThreadSync.Legacy.execute_toy words schedule initial

end Silmaril.Machine.MulticoreVM.ThreadSync.Legacy
