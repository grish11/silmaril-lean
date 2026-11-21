module

public import Silmaril.Wasm.Execution.Core.Intrinsic.OpSem.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Normalize.Thms
public import Silmaril.Semantics.Operational.Policy.Thms

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.OpSem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Intrinsic
  Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Semantics.Operational

variable {H : Type} {context : Context} {world : World H context}
  {locals results : List IntType} {oracle : GrowOracle}

theorem typedReach_iff (state target : State world locals results) :
    typedSem.toOpSem.Reach state target ↔ ∃ fuel, state.runFor fuel = target := by
  constructor
  · intro path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head edge _ ih =>
      obtain ⟨fuel, runs⟩ := ih
      exact ⟨fuel + 1, by simpa [State.runFor, show State.step? _ = some _ from edge] using runs⟩
  · rintro ⟨fuel, rfl⟩
    induction fuel generalizing state with
    | zero => exact .refl
    | succ fuel ih =>
      cases next : state.step? with
      | none => simpa [State.runFor, next] using (Relation.ReflTransGen.refl (r := typedSem.step))
      | some nextState =>
        have path := Relation.ReflTransGen.head (r := typedSem.step) next (ih nextState)
        simpa [State.runFor, next] using path

theorem raw_safe (state : State world locals results) :
    (rawSem oracle (stackTypes results)).SafeAt state.erase :=
  WithUB.enforce_safe_iff.mpr ⟨WithUB.ofOpSem_safe _ _, fun {_} path => state.raw_typed path⟩

theorem may_iff (state : State world locals results) (outcome : Outcome Completion) :
    (rawSem oracle (stackTypes results)).toOpSem.May state.erase outcome ↔ typedSem.toOpSem.May state outcome := by
  have admitted : ∀ ⦃target⦄, (rawOrdinary oracle).Reach state.erase target → ConfigOk target (stackTypes results) :=
    fun {_} path => state.raw_typed path
  refine (WithUB.enforce_may_iff (sem := WithUB.ofOpSem (rawOrdinary oracle)) admitted).trans ?_
  change (∃ target, Steps (profile oracle) noHost state.erase target ∧
      ∃ result, target.code = result.toAdmin ∧ observeResult result = outcome) ↔ _
  constructor
  · rintro ⟨target, path, result, code, observed⟩
    obtain ⟨fuel, returns⟩ := (state.raw_result_iff result).mp ⟨target, path, code⟩
    exact ⟨_, (typedReach_iff state _).mpr ⟨fuel, rfl⟩, result, returns, observed⟩
  · rintro ⟨target, path, result, returned, observed⟩
    obtain ⟨fuel, rfl⟩ := (typedReach_iff state target).mp path
    exact ⟨_, state.runFor_sound fuel, result, (State.result_sound (profile := profile oracle) returned).1, observed⟩

theorem typed_deterministic (state : State world locals results) : typedSem.toOpSem.DetFrom state := by
  intro source _
  constructor
  · intro _ _ left right
    exact Option.some.inj (left.symm.trans right)
  · rintro _ _ ⟨first, left, rfl⟩ ⟨second, right, rfl⟩
    exact congrArg observeResult (Option.some.inj (left.symm.trans right))

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.OpSem
