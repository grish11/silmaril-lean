module

public import Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional.Defs
public import Silmaril.Wasm.Execution.Core.Entry.Determinism.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
import Silmaril.Wasm.Execution.Core.Entry.Thms
import Silmaril.Proofs.Wasm.Execution.Core.Entry.ClosedFunctional

public section

namespace Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional

open Cfg.ProfileFree Numerics Semantics.Operational SingleThreaded SingleThreaded.Det SingleThreaded.Exec Validation

variable {H : Type} {P Q : Profile} {s : Store H} {address : Nat} {args : List Val}
  {types : List CValType} {final : Config H} {result : Result}

theorem raw_free {mode : Profiles.GCMode} (body : Profiles.FunctionalISA.Raw mode) :
    ∀ instr ∈ body.erase, IFree instr := Proofs.Wasm.Execution.Core.Entry.ClosedFunctional.raw_free body

theorem typed_free {ctx mode inputs outputs} (body : Profiles.FunctionalISA.Code mode ctx inputs outputs) :
    ∀ instr ∈ body.erase, IFree instr := raw_free body.toRaw

theorem invoke_free (closed : Bodies s) : ConfigFree (invoke s address args) :=
  Proofs.Wasm.Execution.Core.Entry.ClosedFunctional.invoke_free closed

/-- Every pair of host-free finite executions at any actual numeric profiles
agrees, including on allocated GC objects and traps. No termination premise
is silently inferred from closedness or typing. -/
theorem finishes_unique (closed : Bodies s) {other : Config H} {second : Result}
    (left : Finishes P noHost (invoke s address args) final result)
    (right : Finishes Q noHost (invoke s address args) other second) : final = other ∧ result = second :=
  Proofs.Wasm.Execution.Core.Entry.ClosedFunctional.finishes_unique closed left right

theorem result_det (closed : Bodies s) : (ordinary P noHost).ResultDetAt (invoke s address args) :=
  profileFree_result _ (invoke_free closed)

theorem safe (typed : ConfigOk (invoke s address args) types) :
    (policy P noHost types).SafeAt (invoke s address args) :=
  (policy_safe_and_may (fun {_ _} => noHost_preserves) typed).1

/-- Finite completeness uses the existing Core interpreter; fuel is
existential and need not equal the length of the raw path. -/
theorem finishes_iff_run (closed : Bodies s) (typed : ConfigOk (invoke s address args) types) :
    Finishes P noHost (invoke s address args) final result ↔ final.code = result.toAdmin ∧
      ∃ fuel, runI neverFail fuel (invoke s address args) = (final, true) :=
  Proofs.Wasm.Execution.Core.Entry.ClosedFunctional.finishes_iff_run closed typed

theorem export_may_iff_run (input : ExportInput H)
    (lookup : Game.Accept.exportFunc? input.ready.instance_ input.name = some address)
    (closed : Bodies input.ready.store) (typed : ConfigOk (invoke input.ready.store address input.args) types)
    (outcome : Outcome Intrinsic.Completion) : (rawExport P noHost types).May input outcome ↔
      ∃ final result fuel, runI neverFail fuel (invoke input.ready.store address input.args) = (final, true) ∧
        final.code = result.toAdmin ∧ Intrinsic.observeResult result = outcome :=
  Proofs.Wasm.Execution.Core.Entry.ClosedFunctional.export_may_iff_run input lookup closed typed outcome

end Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional
