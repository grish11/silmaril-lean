module

public import Silmaril.Wasm.Component.InstTests.Defs
public import Silmaril.Wasm.Component.InstEngine.Defs
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# Component test binaries: from the bytes to the litmus modules

* `parse_starts`, `parse_trap`: `Binary.parseComponent` lowers the bytes to `startsComp`,
  `trapComp` (one definitional check by the kernel, `kernel_rfl`);
* `coreModule_*`: the core decoder reads the embedded modules as the litmus modules;
* `startsComp_denI`, `trapComp_denI`: hence the instantiating denotation of the lowered
  components over `Binary.coreModSemI P` is that of `startsC`, `trapLC` over `core3SemI P`
  (the module semantics agree, `sem_*`; the rest of the denotation is the same term).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstTests

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests
open Silmaril.Wasm.Numerics (Profile)

theorem parse_starts : Binary.parseComponent startsBytes = .ok startsComp := by kernel_rfl

theorem parse_trap : Binary.parseComponent trapBytes = .ok trapComp := by kernel_rfl

theorem coreModule_call1 : Binary.coreModule call1CM = callCore3 1 := by kernel_rfl

theorem coreModule_call2 : Binary.coreModule call2CM = callCore3 2 := by kernel_rfl

theorem coreModule_glob : Binary.coreModule globCM = globCore3 := by kernel_rfl

theorem coreModule_trap : Binary.coreModule trapCM = trapCore3 := by kernel_rfl

variable (P : Profile)

theorem sem_call1 : (Binary.coreModSemI P).sem call1CM = (core3SemI P).sem (callMod 1) := by
  simp only [Binary.coreModSemI, core3SemI, engineSemI, coreModule_call1]
  rfl

theorem sem_call2 : (Binary.coreModSemI P).sem call2CM = (core3SemI P).sem (callMod 2) := by
  simp only [Binary.coreModSemI, core3SemI, engineSemI, coreModule_call2]
  rfl

theorem sem_glob : (Binary.coreModSemI P).sem globCM = (core3SemI P).sem globMod := by
  simp only [Binary.coreModSemI, core3SemI, engineSemI, coreModule_glob]
  rfl

theorem sem_trap : (Binary.coreModSemI P).sem trapCM = (core3SemI P).sem trapMod := by
  simp only [Binary.coreModSemI, core3SemI, engineSemI, coreModule_trap]
  rfl

/-- **The lowered `starts.wasm` denotes what `startsC` denotes.** -/
theorem startsComp_denI : startsComp.denI (Binary.coreModSemI P) = startsC.denI (core3SemI P) := by
  simp only [Comp.denI, Comp.denIR, startsComp, startsC, denNodesI, Node.denI, coreNodeI]
  rw [sem_call1, sem_call2, sem_glob]
  rfl

/-- **The lowered `trap.wasm` denotes what `trapLC` denotes.** -/
theorem trapComp_denI : trapComp.denI (Binary.coreModSemI P) = trapLC.denI (core3SemI P) := by
  simp only [Comp.denI, Comp.denIR, trapComp, trapLC, denNodesI, Node.denI, coreNodeI]
  rw [sem_trap, sem_call2]
  rfl

end Silmaril.Proofs.Wasm.Component.InstTests
