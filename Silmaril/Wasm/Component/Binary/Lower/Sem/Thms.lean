module

public import Silmaril.Wasm.Component.Binary.Lower.Sem.Defs
public import Silmaril.Wasm.Component.Param.Start.Thms

/-! # An execution-based core semantics for lowered core modules: theorems

* `coreModule_of_decode`: a lowered module whose bytes decode to `m` is run as `m`.
* `coreModSem_sem_of_inst`: a lowered module with an engine instance (no start function)
  denotes that instance's game semantics (`engineStrategy`).
* The opt-in lazy start variant (`coreModSemLazyStart`, not the specification's start
  semantics): `coreModSemLazyStart_sem_of_instS`, a lowered module with an instance before its
  start function denotes that instance's game semantics with its lazy start phase
  (`engineStrategyS`); `coreModSemLazyStart_eq_coreModSem`, on a module without a start
  function the two semantics agree.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Wasm.Numerics (Profile)

theorem coreModule_of_decode {cm : CoreMod} {m : Silmaril.Wasm.Module}
    (h : Silmaril.Wasm.Binary.Core.decode? cm.bytes = some m) : coreModule cm = m := by
  simp [coreModule, h]

/-- A lowered module with an engine instance (no start function) denotes that instance's game
semantics. -/
theorem coreModSem_sem_of_inst (P : Profile) {cm : CoreMod}
    {I : Silmaril.Wasm.Component.Param.EInstance (Silmaril.Wasm.Component.Reference.core3P P)}
    (h : Silmaril.Wasm.Component.Param.instOf (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some I) :
    (coreModSem P).sem cm = Silmaril.Wasm.Component.Param.engineStrategy _ I
      (CoreModule.imports cm) (CoreModule.exports cm) := by
  simp [coreModSem, Silmaril.Wasm.Component.Param.engineSem, h]

/-- **Opt-in lazy start** (not the specification's start semantics): a lowered module with an
instance before its start function denotes that instance's game semantics with its lazy start
phase. -/
theorem coreModSemLazyStart_sem_of_instS (P : Profile) {cm : CoreMod}
    {I : Silmaril.Wasm.Component.Param.SInstance (Silmaril.Wasm.Component.Reference.core3P P)}
    (h : Silmaril.Wasm.Component.Param.instOfS (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some I) :
    (coreModSemLazyStart P).sem cm = Silmaril.Wasm.Component.Param.engineStrategyS _ I
      (CoreModule.imports cm) (CoreModule.exports cm) := by
  simp [coreModSemLazyStart, Silmaril.Wasm.Component.Param.engineSemS, h]

/-- On a lowered module without a start function, the opt-in lazy start semantics is
`coreModSem`. -/
theorem coreModSemLazyStart_eq_coreModSem (P : Profile) {cm : CoreMod}
    (h : ∀ I, Silmaril.Wasm.Component.Param.instOfS (Silmaril.Wasm.Component.Reference.core3P P)
      (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) = some I → I.start = none) :
    (coreModSemLazyStart P).sem cm = (coreModSem P).sem cm := by
  unfold coreModSemLazyStart coreModSem
  exact Silmaril.Wasm.Component.Param.engineSemS_sem_of_noStart
    (E := Silmaril.Wasm.Component.Reference.core3P P) CoreMod coreModule cm h

end Silmaril.Wasm.Component.Binary
