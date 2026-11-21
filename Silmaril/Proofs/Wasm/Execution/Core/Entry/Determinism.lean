module

public import Silmaril.Wasm.Execution.Core.Entry.Determinism.Defs
public import Silmaril.Semantics.Operational.Determinism.Thms
import Silmaril.Wasm.Execution.Core.Entry.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Thms
import Silmaril.Wasm.Cfg.ProfileFree.Thms
import Silmaril.Wasm.Behaviour.Refinement.Interpreter

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Entry.Determinism

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Entry
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
  Silmaril.Wasm.Cfg.ProfileFree Silmaril.Semantics.Operational

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem driver_valid (head : HeadFn H)
    (sound : ∀ ⦃source target⦄, step? head source = some target → Step P host source target) (source : Config H) :
    (driverDecision head source).Valid (WithUB.ofOpSem (ordinary P host)) source := by
  unfold driverDecision
  split
  · rename_i result computed
    exact ⟨result, codeOutcome?_sound computed, rfl⟩
  · split
    · rename_i target step
      exact sound step
    · trivial

theorem deterministic_result (oracle : GrowOracle) (source : Config H) :
    (ordinary (profile oracle) (noHost : HostSemantics H)).ResultDetAt source := by
  apply OpSem.resultDetAt_iff.mpr
  intro left right leftMay rightMay
  obtain ⟨_, _, leftRun, rfl⟩ := ordinary_may.mp leftMay
  obtain ⟨_, _, rightRun, rfl⟩ := ordinary_may.mp rightMay
  exact congrArg observeResult (finishes_unique leftRun rightRun).2

theorem profileFree_steps {Q : Profile} {source target : Config H}
    (free : ConfigFree source) (path : Steps P noHost source target) : Steps Q noHost source target := by
  have preserved : HostFree (noHost : HostSemantics H) := fun _ _ _ _ _ impossible => impossible.elim
  have result : ConfigFree target ∧ Steps Q noHost source target := by
    induction path with
    | refl => exact ⟨free, .refl⟩
    | tail _ last ih =>
      obtain ⟨funcs, code⟩ := step_free last preserved ih.1.2 ih.1.1
      exact ⟨⟨code, funcs⟩, ih.2.tail (step_profile last ih.1.1)⟩
  exact result.2

theorem profileFree_result (source : Config H) (free : ConfigFree source) :
    (ordinary P (noHost : HostSemantics H)).ResultDetAt source := by
  apply OpSem.resultDetAt_iff.mpr
  intro left right leftMay rightMay
  have transfer (outcome : Outcome Completion) (observed : (ordinary P noHost).May source outcome) :
      (ordinary (profile neverFail) noHost).May source outcome := by
    obtain ⟨target, result, ⟨path, finished⟩, agrees⟩ := ordinary_may.mp observed
    exact ordinary_may.mpr ⟨target, result, ⟨profileFree_steps free path, finished⟩, agrees⟩
  exact OpSem.resultDetAt_iff.mp (deterministic_result neverFail source) (transfer left leftMay) (transfer right rightMay)

end Silmaril.Proofs.Wasm.Execution.Core.Entry.Determinism

namespace Silmaril.Proofs.Wasm.Execution.Core.Entry.Determinism

open Silmaril.Wasm Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.Validation
  Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded Silmaril.Semantics.Operational

variable {H : Type} {context : Context} {world : World H context} {locals results : List IntType}

theorem normal_valid (state : State world locals results) : (normalDecision state).Valid typedSem state := by
  unfold normalDecision
  split
  · assumption
  · split
    · rename_i result finishes
      exact ⟨result, finishes, rfl⟩
    · trivial

theorem normal_terminal : (typedSem (world := world) (locals := locals) (results := results)).toOpSem.TerminalDiscipline := by
  rintro ⟨frame, control⟩ outcome ⟨result, finishes, _⟩ next step
  change State.step? ⟨frame, control⟩ = some next at step
  cases control with
  | run stack code => cases code <;> simp [State.result?, State.step?, Control.result?, Control.step?] at finishes step
  | trapping stack tail =>
    by_cases empty : stack.isEmpty && tail.isEmpty
    · simp [State.step?, Control.step?, empty] at step
    · simp [State.result?, Control.result?, empty] at finishes

theorem normal_known (state : State world locals results) : normalDecision state ≠ .stop .unknown := by
  obtain ⟨frame, control⟩ := state
  cases control with
  | run stack code => cases code <;> simp [normalDecision, State.result?, State.step?, Control.result?, Control.step?]
  | trapping stack tail =>
    by_cases empty : stack.isEmpty && tail.isEmpty <;>
      simp [normalDecision, State.result?, State.step?, Control.result?, Control.step?, empty]

end Silmaril.Proofs.Wasm.Execution.Core.Entry.Determinism
