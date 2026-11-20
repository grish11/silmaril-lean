module

public import Silmaril.Wasm.Component.Binary.Lower.Sem.Defs

/-! # An execution-based core semantics for lowered core modules: theorems

* `coreModule_of_decode`: a lowered module whose bytes decode to `m` is run as `m`.
* `coreModSem_sem_of_inst`: a lowered module with an engine instance denotes that instance's
  game semantics (`engineStrategy`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Wasm.Numerics (Profile)

theorem coreModule_of_decode {cm : CoreMod} {m : Silmaril.Wasm.Module}
    (h : Silmaril.Wasm.Binary.Core.decode? cm.bytes = some m) : coreModule cm = m := by
  simp [coreModule, h]

/-- A lowered module with an engine instance denotes that instance's game semantics. -/
theorem coreModSem_sem_of_inst (P : Profile) {cm : CoreMod}
    {I : Silmaril.Wasm.Component.Param.EInstance (Silmaril.Wasm.Component.Reference.core3P P)}
    (h : Silmaril.Wasm.Component.Param.instOf (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some I) :
    (coreModSem P).sem cm = Silmaril.Wasm.Component.Param.engineStrategy _ I
      (CoreModule.imports cm) (CoreModule.exports cm) := by
  simp [coreModSem, Silmaril.Wasm.Component.Param.engineSem, h]

end Silmaril.Wasm.Component.Binary
