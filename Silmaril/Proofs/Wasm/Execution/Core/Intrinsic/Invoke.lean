module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Invoke.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Thms
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Invoke

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec Silmaril.Wasm.SingleThreaded.Det
open BehaviourRefinement

variable {H : Type} {leftCtx rightCtx : Context} {left : World H leftCtx}
  {right : World H rightCtx} {parameters results : List IntType} {oracle : GrowOracle}

private theorem values_iff (store : Store H) (types : List IntType) (vs : List Val) :
    List.Forall₂ (ValOk store) vs (stackTypes types.reverse) ↔
      ∃ args : Values types, args.erase = vs := by
  simp only [stackTypes, List.map_reverse, List.reverse_reverse]
  induction types generalizing vs with
  | nil =>
    constructor
    · intro typed
      cases typed
      exact ⟨.nil, rfl⟩
    · rintro ⟨args, rfl⟩
      cases args
      exact .nil
  | cons kind tail ih =>
    constructor
    · intro typed
      cases typed with
      | cons head rest =>
        obtain ⟨bits, rfl⟩ := head.int_inv
        obtain ⟨args, rfl⟩ := (ih _).mp rest
        exact ⟨.cons bits args, rfl⟩
    · rintro ⟨args, rfl⟩
      cases args with
      | cons bits tailArgs => exact .cons (.num _) ((ih _).mpr ⟨tailArgs, rfl⟩)

theorem invokeOk_iff (call : DirectCall left parameters results) (vs : List Val) :
    InvokeOk left.store call.address vs ↔ ∃ args : Values parameters, args.erase = vs := by
  constructor
  · rintro ⟨entry, ps, rs, found, expanded, typed⟩
    have same := Option.some.inj (found.symm.trans call.resolveAddress)
    subst entry
    have signature := Expand.func_eq expanded call.signature
    injection signature with hp _
    rw [hp, Ty.toList_ofList] at typed
    exact (values_iff left.store parameters vs).mp (by simpa [stackTypes] using typed)
  · intro typed
    refine ⟨call.instance_, _, _, call.resolveAddress, call.signature, ?_⟩
    simpa [Ty.toList_ofList, stackTypes] using (values_iff left.store parameters vs).mpr typed

private theorem not_diverges_of_normal_form {start final : Config H}
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

theorem invoke_not_diverges (call : DirectCall left parameters results) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (returned : call.runFor args fuel = some answer) :
    ¬ Diverges (profile oracle) noHost (invoke left.store call.address args.erase) := by
  let final : Config H := ⟨left.store, {}, (invokeResult answer).toAdmin⟩
  have steps : Steps (profile oracle) noHost (invoke left.store call.address args.erase) final := by
    cases answer <;> exact call.invoke_sound args fuel returned
  exact not_diverges_of_normal_form steps (fun _ => not_step_of_terminal ⟨invokeResult answer, rfl⟩)

theorem invoke_behaviours (call : DirectCall left parameters results) (args : Values parameters)
    {fuel : Nat} {answer : Option (Values results)} (returned : call.runFor args fuel = some answer) :
    behaviours (profile oracle) noHost left.store call.address args.erase = {(invokeResult answer).toBehaviour} := by
  let final : Config H := ⟨left.store, {}, (invokeResult answer).toAdmin⟩
  have steps : Steps (profile oracle) noHost (invoke left.store call.address args.erase) final := by
    cases answer <;> exact call.invoke_sound args fuel returned
  have terminal : final.Terminal := ⟨invokeResult answer, rfl⟩
  exact behavioursOf_eq_singleton_of_steps_nf steps (fun _ => not_step_of_terminal terminal) rfl
    (invoke_not_diverges call args returned)

theorem invocations_eq_iff (first : DirectCall left parameters results)
    (second : DirectCall right parameters results) (args : Values parameters)
    {firstFuel secondFuel : Nat} {firstAnswer secondAnswer : Option (Values results)}
    (firstRun : first.runFor args firstFuel = some firstAnswer)
    (secondRun : second.runFor args secondFuel = some secondAnswer) :
    behaviours (profile oracle) noHost left.store first.address args.erase =
        behaviours (profile oracle) noHost right.store second.address args.erase ↔
      (invokeResult firstAnswer).toBehaviour = (invokeResult secondAnswer).toBehaviour := by
  rw [invoke_behaviours first args firstRun, invoke_behaviours second args secondRun]
  exact ⟨fun equal => Set.singleton_injective equal, congrArg Set.singleton⟩

theorem entry_eq (first : DirectCall left parameters results) (second : DirectCall right parameters results)
    (runs : ∀ args, ∃ firstFuel secondFuel answer,
      first.runFor args firstFuel = some answer ∧ second.runFor args secondFuel = some answer) :
    EntryAgreement Eq (profile oracle) noHost left.store right.store first.address second.address := by
  refine ⟨fun vs => (invokeOk_iff first vs).trans (invokeOk_iff second vs).symm, ?_⟩
  intro vs accepted
  obtain ⟨args, rfl⟩ := (invokeOk_iff first vs).mp accepted
  obtain ⟨_, _, _, firstRun, secondRun⟩ := runs args
  rw [(invocations_eq_iff first second args firstRun secondRun).mpr rfl]
  exact ⟨fun observation member => ⟨observation, member, rfl⟩,
    fun observation member => ⟨observation, member, rfl⟩⟩

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Invoke
