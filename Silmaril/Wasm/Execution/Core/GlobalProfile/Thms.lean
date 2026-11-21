module

public import Silmaril.Wasm.Execution.Core.GlobalProfile.Defs
import Silmaril.Proofs.Wasm.Execution.Core.GlobalProfile

public section

namespace Silmaril.Wasm.Execution.Core.GlobalProfile

open Numerics Semantics.Operational SingleThreaded.Det
open Intrinsic (Values stackTypes Completion observeResult)

variable {P : Profile} {mutability : Mutability} {input output : List IntType}

theorem start_typed (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    ConfigOk (code.start stack value) (stackTypes output) :=
  Proofs.Wasm.Execution.Core.GlobalProfile.start_typed code stack value

theorem eval_finishes (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    Entry.Finishes P noHost (code.start stack value) ((code.eval stack value).erase mutability)
      (code.eval stack value).result :=
  Proofs.Wasm.Execution.Core.GlobalProfile.eval_finishes code stack value

/-- Sound and complete for finite Core results from these entries, with store
and frame equality, at every actual Core numeric profile. -/
theorem finishes_iff (code : Code mutability input output) (stack : Values input) (value : BitVec 32)
    (final : Config Empty) (result : Result) : Entry.Finishes P noHost (code.start stack value) final result ↔
      final = (code.eval stack value).erase mutability ∧ result = (code.eval stack value).result :=
  Proofs.Wasm.Execution.Core.GlobalProfile.finishes_iff code stack value final result

theorem safe_and_may (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    (Entry.policy P noHost (stackTypes output)).SafeAt (code.start stack value) ∧
      ∀ outcome : Outcome Completion, (Entry.policy P noHost (stackTypes output)).toOpSem.May
        (code.start stack value) outcome ↔ outcome = observeResult (code.eval stack value).result :=
  Proofs.Wasm.Execution.Core.GlobalProfile.safe_and_may code stack value

/-- Absence of an infinite Core path follows from profile transfer and the
host-free normalization theorem, not from the interpreter's termination alone. -/
theorem not_diverges (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    ¬ Diverges P noHost (code.start stack value) :=
  Proofs.Wasm.Execution.Core.GlobalProfile.not_diverges code stack value

end Silmaril.Wasm.Execution.Core.GlobalProfile
