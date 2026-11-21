module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Normalize.Defs
public import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
public import Silmaril.Wasm.SingleThreaded.Profile
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Normalize

public section

namespace Silmaril.Wasm.Execution.Core.Intrinsic

open Numerics Validation SingleThreaded SingleThreaded.Det

variable {H : Type} {context : Context} {world : World H context}
  {locals results : List IntType} {oracle : GrowOracle}

theorem State.finishes (state : State world locals results) :
    ∃ fuel result, (state.runFor fuel).result? = some result :=
  Proofs.Wasm.Execution.Core.Intrinsic.Normalize.finishes state

/-- Read back all reachable raw normal forms, not all intermediate raw states.
Core can take extra administrative steps to bubble traps. -/
theorem State.raw_normal_iff (state : State world locals results) (target : Config H) :
    (Steps (profile oracle) noHost state.erase target ∧
      ∀ next, ¬ Step (profile oracle) noHost target next) ↔
      ∃ fuel result, (state.runFor fuel).result? = some result ∧ target = (state.runFor fuel).erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.Normalize.raw_normal_iff state target

theorem State.raw_result_iff (state : State world locals results) (result : Result) :
    (∃ target, Steps (profile oracle) noHost state.erase target ∧ target.code = result.toAdmin) ↔
      ∃ fuel, (state.runFor fuel).result? = some result :=
  Proofs.Wasm.Execution.Core.Intrinsic.Normalize.raw_result_iff state result

/-- Even if a raw prefix stops partway through trap propagation, it can
continue to the same erased normal form that the typed evaluator computes. -/
theorem State.raw_prefix_finishes (state : State world locals results) {target : Config H}
    (prefixPath : Steps (profile oracle) noHost state.erase target) :
    ∃ fuel result, (state.runFor fuel).result? = some result ∧
      Steps (profile oracle) noHost target (state.runFor fuel).erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.Normalize.raw_prefix_finishes state prefixPath

/-- All raw prefixes, including partial trap propagation, preserve Core typing. -/
theorem State.raw_typed {P : Profile} (state : State world locals results) {target : Config H}
    (reaches : Steps P noHost state.erase target) : ConfigOk target (stackTypes results) :=
  Proofs.Wasm.Execution.Core.Intrinsic.Normalize.raw_typed state reaches

theorem State.raw_not_typingUB {P : Profile} (state : State world locals results) {target : Config H}
    (reaches : Steps P noHost state.erase target) : ¬ typingUB (stackTypes results) target :=
  fun bad => bad (state.raw_typed reaches)

theorem State.raw_not_diverges (state : State world locals results) :
    ¬ Diverges (profile oracle) noHost state.erase :=
  Proofs.Wasm.Execution.Core.Intrinsic.Normalize.raw_not_diverges state

/-- Unique normal forms alone do not rule out divergence. This result also
uses the shrinkage of competing host-free administrative steps. -/
theorem noHost_not_diverges_of_normal_form {start final : Config H}
    (steps : Steps (profile oracle) noHost start final)
    (normal : ∀ next, ¬ Step (profile oracle) noHost final next) :
    ¬ Diverges (profile oracle) noHost start :=
  Proofs.Wasm.Execution.Core.Intrinsic.Normalize.not_diverges_of_normal_form steps normal

end Silmaril.Wasm.Execution.Core.Intrinsic
