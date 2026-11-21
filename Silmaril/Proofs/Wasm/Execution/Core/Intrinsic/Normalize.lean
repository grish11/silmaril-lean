module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Normalize.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Normalize

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Wasm.SingleThreaded.Exec BehaviourRefinement

variable {H : Type} {context : Context} {world : World H context}
  {locals results : List IntType} {oracle : GrowOracle}

private theorem trapping_finishes (frame : LocalFrame world locals) {saved ignored : List IntType}
    (stack : Values saved) (code : Code locals ignored results) :
    ∃ fuel result, ((State.mk frame (.trapping stack code)).runFor fuel).result? = some result := by
  by_cases empty : (stack.isEmpty && code.isEmpty) = true
  · exact ⟨0, .trap, by simp [State.runFor, State.result?, Control.result?, empty]⟩
  · have first : (State.mk frame (.trapping stack code)).step? =
        some (State.mk frame (.trapping .nil .done)) := by
      simp only [State.step?, Control.step?, ite_eq_right empty, Option.map_some]
    exact ⟨1, .trap, by simp only [State.runFor, first]; rfl⟩

private theorem run_finishes (frame : LocalFrame world locals) {input : List IntType}
    (code : Code locals input results) : ∀ stack : Values input,
    ∃ fuel result, ((State.mk frame (.run stack code)).runFor fuel).result? = some result := by
  induction code with
  | done => intro stack; exact ⟨0, .values stack.erase.reverse, rfl⟩
  | seq op tail ih =>
    intro stack
    cases evaluated : op.eval frame.values stack with
    | next values =>
      obtain ⟨fuel, result, returned⟩ := ih values
      exact ⟨fuel + 1, result, by
        simpa [State.runFor, State.step?, Control.step?, evaluated, Effect.resume] using returned⟩
    | trap values =>
      obtain ⟨fuel, result, returned⟩ := trapping_finishes frame values tail
      exact ⟨fuel + 1, result, by
        simpa [State.runFor, State.step?, Control.step?, evaluated, Effect.resume] using returned⟩

theorem finishes (state : State world locals results) :
    ∃ fuel result, (state.runFor fuel).result? = some result := by
  obtain ⟨frame, control⟩ := state
  cases control with
  | run stack code => exact run_finishes frame code stack
  | trapping stack code => exact trapping_finishes frame stack code

theorem raw_normal_iff (state : State world locals results) (target : Config H) :
    (Steps (profile oracle) noHost state.erase target ∧ ∀ next, ¬ DStep oracle target next) ↔
      ∃ fuel result, (state.runFor fuel).result? = some result ∧ target = (state.runFor fuel).erase := by
  constructor
  · rintro ⟨reaches, stopped⟩
    obtain ⟨fuel, result, returned⟩ := finishes state
    exact ⟨fuel, result, returned, eq_of_steps_of_nf reaches (state.runFor_sound fuel)
      stopped (State.result_sound returned).2⟩
  · rintro ⟨fuel, result, returned, rfl⟩
    exact ⟨state.runFor_sound fuel, (State.result_sound returned).2⟩

theorem raw_result_iff (state : State world locals results) (result : Result) :
    (∃ target, Steps (profile oracle) noHost state.erase target ∧ target.code = result.toAdmin) ↔
      ∃ fuel, (state.runFor fuel).result? = some result := by
  constructor
  · rintro ⟨target, reaches, code⟩
    obtain ⟨fuel, answer, returned, rfl⟩ := (raw_normal_iff state target).mp
      ⟨reaches, fun _ => not_step_of_terminal ⟨result, code⟩⟩
    have actual := outcome?_eq_some_of_code (State.result_sound (profile := profile oracle) returned).1
    have expected := outcome?_eq_some_of_code code
    exact ⟨fuel, (Option.some.inj (actual.symm.trans expected)) ▸ returned⟩
  · rintro ⟨fuel, returned⟩
    exact ⟨_, state.runFor_sound fuel, (State.result_sound (profile := profile oracle) returned).1⟩

theorem raw_prefix_finishes (state : State world locals results) {target : Config H}
    (prefixPath : Steps (profile oracle) noHost state.erase target) :
    ∃ fuel result, (state.runFor fuel).result? = some result ∧
      Steps (profile oracle) noHost target (state.runFor fuel).erase := by
  obtain ⟨fuel, result, returned⟩ := finishes state
  obtain ⟨_, prefixTail, typedTail⟩ := Relation.church_rosser (step_subcommutative oracle)
    prefixPath (state.runFor_sound fuel)
  have same := Silmaril.Wasm.Behaviour.Refinement.eq_of_normalForm typedTail (State.result_sound returned).2
  exact ⟨fuel, result, returned, same.symm ▸ prefixTail⟩

theorem raw_typed {P : Profile} (state : State world locals results) {target : Config H}
    (reaches : Steps P noHost state.erase target) : ConfigOk target (stackTypes results) := by
  let divergentHost : HostSemantics H := fun _ _ _ outcome => outcome = .diverged
  have hostOk : HostOk divergentHost := by
    intro store entry func args params returns _ _ _ _ _
    exact ⟨⟨.diverged, rfl⟩, fun outcome equal => by cases equal; trivial⟩
  have widened : Steps P divergentHost state.erase target :=
    Relation.ReflTransGen.mono (fun _ _ step => Step.of_noHost divergentHost step) _ _ reaches
  exact (Steps.safe hostOk state.sound widened).1

theorem not_diverges_of_normal_form {start final : Config H}
    (steps : Steps (profile oracle) noHost start final)
    (normal : ∀ next, ¬ DStep oracle final next) : ¬ Diverges (profile oracle) noHost start := by
  have bounded : ∀ count size (source : Config H), sizeOf source.code = size →
      NSteps (DStep oracle) count source final → ¬ Diverges (profile oracle) noHost source := by
    intro count
    induction count using Nat.strong_induction_on with
    | _ count fewer =>
      intro size
      induction size using Nat.strong_induction_on with
      | _ size smaller =>
        intro source sourceSize path infinite
        obtain ⟨next, step, infiniteNext⟩ := infinite.unfold
        cases path with
        | refl => exact normal next step
        | @head _ chosen _ tail chosenStep remaining =>
          rcases source with ⟨store, frame, code⟩
          rcases DStep.shrink size store frame code next chosen sourceSize step chosenStep with
            equal | ⟨_, _, shrinks, _⟩
          · exact fewer tail (by omega) _ _ rfl remaining (equal ▸ infiniteNext)
          · obtain ⟨distance, le, path⟩ := NSteps.of_step_join
              (fun first second => DStep.join' first second) normal (.head chosenStep remaining) step
            rcases Nat.lt_or_eq_of_le le with shorter | same
            · exact fewer distance shorter _ _ rfl path infiniteNext
            · exact smaller _ (sourceSize ▸ shrinks) _ rfl (same ▸ path) infiniteNext
  obtain ⟨count, counted⟩ := NSteps.of_rtg steps
  exact bounded count _ start rfl counted

theorem raw_not_diverges (state : State world locals results) :
    ¬ Diverges (profile oracle) noHost state.erase := by
  obtain ⟨fuel, _, returned⟩ := finishes state
  exact not_diverges_of_normal_form (state.runFor_sound fuel) (State.result_sound returned).2

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Normalize
