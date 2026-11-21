module

public import Silmaril.Wasm.Profiles.Functional.Defs
public import Silmaril.Wasm.Profiles.Thms
import Silmaril.Proofs.Wasm.Profiles.FunctionalISA

public section

namespace Silmaril.Wasm.Profiles.FunctionalISA

open Validation Models

theorem TypedAtom.sound {ctx gc inputs outputs} (atom : TypedAtom ctx gc inputs outputs) :
    InstrOk ctx atom.toRaw.erase (.plain inputs outputs) := Proofs.Wasm.Profiles.FunctionalISA.atom_sound atom

theorem Code.sound {gc ctx inputs outputs} (code : Code gc ctx inputs outputs) :
    InstrsOk ctx code.erase (.plain inputs outputs) := Proofs.Wasm.Profiles.FunctionalISA.code_sound code

/-- Lifting preserves the erased expression, not the witness tree. -/
theorem Code.liftCore {gc ctx inputs outputs} (code : Code gc ctx inputs outputs) :
    ∃ body : Intrinsic.Body ctx (.plain inputs outputs), body.erase = code.erase :=
  Intrinsic.Body.lift_erase code.sound

theorem Raw.features {gc} (raw : Raw gc) (exceptions : ExceptionMode) :
    Instr.insInFeatB (FunctionalCore.features gc exceptions) raw.erase = true :=
  Proofs.Wasm.Profiles.FunctionalISA.raw_features raw exceptions

theorem Code.features {gc ctx inputs outputs} (code : Code gc ctx inputs outputs) (exceptions : ExceptionMode) :
    Instr.insInFeatB (FunctionalCore.features gc exceptions) code.erase = true := code.toRaw.features exceptions

@[simp] theorem Raw.allowWrites_erase (raw : Raw .immutable) : raw.allowWrites.erase = raw.erase :=
  Proofs.Wasm.Profiles.FunctionalISA.allowWrites_erase raw

end Silmaril.Wasm.Profiles.FunctionalISA
