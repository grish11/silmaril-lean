module

public import Silmaril.Wasm.Component.Binary.Lower.Sem.Defs
public import Silmaril.Wasm.Component.Param.Start.Thms

/-! # An execution-based core semantics for lowered core modules: theorems

* `coreModule_of_decode`: a lowered module whose bytes decode to `m` is run as `m`.
* `coreModSem_sem_of_inst`: a lowered module with an engine instance (no start function)
  denotes that instance's game semantics (`engineStrategy`);
* `coreModSem_sem_of_instS`: a lowered module with an instance before its start function
  denotes that instance's game semantics with its start phase (`engineStrategyS`);
* `coreModSem_eq_engineSem`: on a module without a start function, `coreModSem P` is the
  start-free `engineSem` it was defined as before.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Wasm.Numerics (Profile)

theorem coreModule_of_decode {cm : CoreMod} {m : Silmaril.Wasm.Module}
    (h : Silmaril.Wasm.Binary.Core.decode? cm.bytes = some m) : coreModule cm = m := by
  simp [coreModule, h]

/-- A lowered module with an instance before its start function denotes that instance's game
semantics with its start phase. -/
theorem coreModSem_sem_of_instS (P : Profile) {cm : CoreMod}
    {I : Silmaril.Wasm.Component.Param.SInstance (Silmaril.Wasm.Component.Reference.core3P P)}
    (h : Silmaril.Wasm.Component.Param.instOfS (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some I) :
    (coreModSem P).sem cm = Silmaril.Wasm.Component.Param.engineStrategyS _ I
      (CoreModule.imports cm) (CoreModule.exports cm) := by
  simp [coreModSem, Silmaril.Wasm.Component.Param.engineSemS, h]

/-- On a lowered module without a start function, `coreModSem P` is `engineSem`. -/
theorem coreModSem_eq_engineSem (P : Profile) {cm : CoreMod}
    (h : ∀ I, Silmaril.Wasm.Component.Param.instOfS (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some I → I.start = none) :
    (coreModSem P).sem cm = (Silmaril.Wasm.Component.Param.engineSem
      (Silmaril.Wasm.Component.Reference.core3P P) CoreMod coreModule).sem cm := by
  unfold coreModSem
  exact Silmaril.Wasm.Component.Param.engineSemS_sem_of_noStart
    (E := Silmaril.Wasm.Component.Reference.core3P P) CoreMod coreModule cm h

/-- A lowered module with an engine instance (no start function) denotes that instance's game
semantics. -/
theorem coreModSem_sem_of_inst (P : Profile) {cm : CoreMod}
    {I : Silmaril.Wasm.Component.Param.EInstance (Silmaril.Wasm.Component.Reference.core3P P)}
    (h : Silmaril.Wasm.Component.Param.instOf (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some I) :
    (coreModSem P).sem cm = Silmaril.Wasm.Component.Param.engineStrategy _ I
      (CoreModule.imports cm) (CoreModule.exports cm) := by
  have hS : ∀ J, Silmaril.Wasm.Component.Param.instOfS (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some J →
      J.start = none := by
    intro J hJ
    have h' := (Silmaril.Wasm.Component.Param.instOf_eq (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm)).symm.trans h
    rw [hJ] at h'
    revert h'
    rcases hs : J.start with _ | a <;> simp [hs]
  rw [coreModSem_eq_engineSem P hS]
  simp [Silmaril.Wasm.Component.Param.engineSem, h]

end Silmaril.Wasm.Component.Binary
