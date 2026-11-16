module

public import Silmaril.Wasm.Component.Param.StartCore3.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Sem.Defs
import Silmaril.Proofs.Wasm.Component.Param.StartCore3

/-!
# Start functions on the Core 3.0 engine: regressions

All proved, by kernel evaluation of the instances (`prepareE?`, and `Binary.Core.decode?` for
the binaries) and Core 3.0 runs built from `Step` rules; proofs in
`Silmaril.Proofs.Wasm.Component.Param.StartCore3`.

**The gap.** `startModEngineSem_eq_trapAll`: under the start-free `engineSem`, the module
`Reference.Litmus.startMod`, whose start function stores `42` in a global, traps on every
question, at every profile.

**The default.** `startCM_coreModSem_eq_trapAll`: the binary `startCM` under the default
`Binary.coreModSem` (start-free `engineSem`) also traps on every question.

**The opt-in lazy start semantics** (`Binary.coreModSemLazyStart`, `Param.engineSemS`). It runs
a start function at the first export question. This is **not** the Component Model's start
semantics, which runs start functions at instantiation (`Binary.Lower.Sem.Defs`). The
regressions below are about the lazy semantics only.

**A start function that returns** (`startMod`, and its binary `startCM` under
`Binary.coreModSemLazyStart`), at every profile `P`:

* `startMod_get`, `startCM_get`: `get()` answers `i32 42`, the value the start function stored;
* `startMod_ne_trapAll`, `startCM_ne_trapAll`: so the module is not `trapAll`.

**A start function that traps** (`trapStartMod`, and its binary `trapCM`):

* `trapStartMod_get`, `trapCM_get`: at every profile, `get()` may be answered by a trap;
* `trapStartMod_eq_trapAll`, `trapCM_eq_trapAll`: at a deterministic profile `profile o`, the
  module traps on every question (although `get` alone would return `7`). The start run can
  reach no other outcome because host-free runs at `profile o` reach at most one normal form.

Not shown: that `get()` of `startMod` can only answer `42` (that needs determinism, as for
`trapStartMod`), or a regression whose start function calls an import (the general statement is
`Param.engineStrategyS_start_call`).
-/

public section

namespace Silmaril.Wasm.Component.Param.StartCore3

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.Litmus (startMod)
open Silmaril.Wasm.Numerics (Profile)

-- Elaborating the statements below must not decode the binaries (`coreModule` is evaluated in
-- the kernel by the proofs, not by the elaborator's `whnf`).
attribute [local irreducible] Silmaril.Wasm.Component.Binary.coreModule

/-- **Under the start-free `engineSem`, `startMod` traps on every question.** -/
theorem startModEngineSem_eq_trapAll (P : Profile) :
    (engineSem (core3P P) NumModule NumModule.mod).sem startMod = trapAll _ _ :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.startMod_engineSem P

/-- **`get()` answers `42`, the value the start function stored.** -/
theorem startMod_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ (some (.flat [Flat.i32 42])))] ∈
      (engineSemS (core3P P) NumModule NumModule.mod).sem startMod :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.startMod_sem_get P

theorem startMod_ne_trapAll (P : Profile) :
    (engineSemS (core3P P) NumModule NumModule.mod).sem startMod ≠ trapAll _ _ :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.startMod_sem_ne_trapAll P

/-- **A trapping start function: `get()` may be answered by a trap**, at every profile. -/
theorem trapStartMod_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ none)] ∈
      (engineSemS (core3P P) NumModule NumModule.mod).sem trapStartMod :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.trapStartMod_sem_get P

/-- **A trapping start function makes every question trap**, at a deterministic profile. -/
theorem trapStartMod_eq_trapAll (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    (engineSemS (core3P (Silmaril.Wasm.SingleThreaded.profile o)) NumModule NumModule.mod).sem
      trapStartMod = trapAll _ _ :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.trapStartMod_sem_eq_trapAll o

/-- **The binary `startCM` under the default `coreModSem` traps on every question** (start-free
`engineSem`: a module with a start function has no engine instance). -/
theorem startCM_coreModSem_eq_trapAll (P : Profile) :
    (Silmaril.Wasm.Component.Binary.coreModSem P).sem startCM = trapAll _ _ :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.startCM_coreModSem P

/-- **The binary `startCM` under `coreModSemLazyStart`: `get()` answers `42`.** -/
theorem startCM_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ (some (.flat [Flat.i32 42])))] ∈
      (Silmaril.Wasm.Component.Binary.coreModSemLazyStart P).sem startCM :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.startCM_get P

theorem startCM_ne_trapAll (P : Profile) :
    (Silmaril.Wasm.Component.Binary.coreModSemLazyStart P).sem startCM ≠ trapAll _ _ :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.startCM_ne_trapAll P

/-- The binary `trapCM` under `coreModSemLazyStart`: `get()` may be answered by a trap. -/
theorem trapCM_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ none)] ∈
      (Silmaril.Wasm.Component.Binary.coreModSemLazyStart P).sem trapCM :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.trapCM_get P

/-- **The binary `trapCM` under `coreModSemLazyStart` traps on every question**, at a deterministic
profile. -/
theorem trapCM_eq_trapAll (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    (Silmaril.Wasm.Component.Binary.coreModSemLazyStart (Silmaril.Wasm.SingleThreaded.profile o)).sem
      trapCM = trapAll _ _ :=
  Silmaril.Proofs.Wasm.Component.Param.StartCore3.trapCM_eq_trapAll o

end Silmaril.Wasm.Component.Param.StartCore3
