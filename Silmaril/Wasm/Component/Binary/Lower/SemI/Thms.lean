module

public import Silmaril.Wasm.Component.Binary.Lower.SemI.Defs
public import Silmaril.Wasm.Component.InstEngine.Thms
public import Silmaril.Wasm.Component.InstExport.Thms
import Silmaril.Proofs.Wasm.Component.Binary.Lower.SemI.Basic

/-! # Lowered core modules with their start functions: theorems

All proved; proofs in `Silmaril.Proofs.Wasm.Component.Binary.Lower.SemI.Basic` and the engine
theorems of `Silmaril.Wasm.Component.InstEngine.Thms`.

**Start-free modules** (`StartFree P cm`: an engine instance, no start function):

* `coreModSemI_after_iff`: a successful instantiation of `cm` makes no import call, and the
  plays after it are exactly those of `coreModSem P` (the restriction theorem);
* `exportPhase_coreModSemI`: the export phase of `cm` is `(coreModSem P).sem cm`;
* `coreModSemI_le_toI`: `cm` is bounded by `coreModSem P` ready at once;
* `denX_coreModSemI_le`: for a lowered component all of whose core modules are start-free, the
  export phase under `coreModSemI P` is bounded by `c.denU (coreModSem P)`. The converse
  inclusion is not proved (see `InstExport.Thms`).

**Modules with a start function** (`instOfI … = some J`, `J.start = some a`):

* `coreModSemI_after_start_iff`: after `[inst] ++ cs ++ [ready]`, exactly the plays of the
  engine instance from a store some start run with the calls `cs` returns at;
* `coreModSemI_after_start_iff_det`: at a deterministic profile `profile o`, exactly the plays
  from the one store the start run returns at.
-/

public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (liftMove)

variable {P : Profile} {cm : CoreMod}

/-- `coreModSemI` is the engine semantics with an instantiation phase of the decoded module. -/
theorem coreModSemI_sem (P : Profile) (cm : CoreMod) :
    (coreModSemI P).sem cm = engineStrategyI (core3P P)
      (instOfI (core3P P) (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm))
      (CoreModule.imports cm) (CoreModule.exports cm) := rfl

/-- **The restriction theorem for lowered modules**: on a start-free module, a successful
instantiation makes no import call, and the plays after it are exactly those of `coreModSem`. -/
theorem coreModSemI_after_iff (h : StartFree P cm)
    (cs : List (Σ _ : (sigN (CoreModule.imports cm).length).Op, Option Payload))
    (p : List (Move (sigN (CoreModule.imports cm).length) (sigN (CoreModule.exports cm).length))) :
    instPlay (F := sigN (CoreModule.exports cm).length) cs .ready ++ p.map liftMove ∈
        (coreModSemI P).sem cm ↔ cs = [] ∧ p ∈ (coreModSem P).sem cm :=
  Silmaril.Proofs.Wasm.Component.Binary.SemI.coreModSemI_after_iff h cs p

/-- **The export phase of a start-free lowered module is its `coreModSem` strategy.** -/
theorem exportPhase_coreModSemI (h : StartFree P cm) :
    exportPhase ((coreModSemI P).sem cm) = (coreModSem P).sem cm :=
  Silmaril.Proofs.Wasm.Component.Binary.SemI.exportPhase_coreModSemI h

/-- A start-free lowered module is bounded by `coreModSem`, ready at once. -/
theorem coreModSemI_le_toI (h : StartFree P cm) :
    (coreModSemI P).sem cm ≤ (coreModSem P).toI.sem cm :=
  Silmaril.Proofs.Wasm.Component.Binary.SemI.coreModSemI_le_toI h

/-- **The export phase of a start-free lowered component is bounded by its `coreModSem`
denotation.** -/
theorem denX_coreModSemI_le {c : Comp CoreMod} (hc : c.AllCore (StartFree P)) :
    c.denX (coreModSemI P) ≤ c.denU (coreModSem P) :=
  Silmaril.Proofs.Wasm.Component.Binary.SemI.denX_coreModSemI_le hc

/-- **After a start function: the export phase of a lowered module**, exactly: the plays of the
engine instance from a store some start run with the calls `cs` returns at. -/
theorem coreModSemI_after_start_iff {J : IInstance (core3P P)} {a : Nat}
    (hJ : instOfI (core3P P) (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) =
      some J) (ha : J.start = some a)
    (cs : List (Σ _ : (sigN (CoreModule.imports cm).length).Op, Option Payload))
    (p : List (Move (sigN (CoreModule.imports cm).length) (sigN (CoreModule.exports cm).length))) :
    instPlay (F := sigN (CoreModule.exports cm).length) cs .ready ++ p.map liftMove ∈
        (coreModSemI P).sem cm ↔
      ∃ (c' : (core3P P).Config Nat) (ys : List Flat),
        StartRunI (core3P P) (CoreModule.imports cm) (J.store, (core3P P).invoke a []) cs c' ∧
        (core3P P).status c'.1 c'.2 = .returned (.values ys) ∧
        p ∈ engineStrategy (core3P P) ⟨c'.1, J.addrs⟩ (CoreModule.imports cm)
          (CoreModule.exports cm) :=
  engineStrategyI_after_start_iff hJ ha cs p

/-- **After a start function, at a deterministic profile**: exactly the plays of the engine
instance from the store the start run with the calls `cs` returns at. -/
theorem coreModSemI_after_start_iff_det {o : Silmaril.Wasm.SingleThreaded.GrowOracle}
    {J : IInstance (core3P (Silmaril.Wasm.SingleThreaded.profile o))} {a : Nat}
    (hJ : instOfI (core3P (Silmaril.Wasm.SingleThreaded.profile o)) (coreModule cm)
      (CoreModule.imports cm) (CoreModule.exports cm) = some J) (ha : J.start = some a)
    {cs : List (Σ _ : (sigN (CoreModule.imports cm).length).Op, Option Payload)}
    {c' : (core3P (Silmaril.Wasm.SingleThreaded.profile o)).Config Nat}
    (hr : StartRunI (core3P (Silmaril.Wasm.SingleThreaded.profile o)) (CoreModule.imports cm)
      (J.store, (core3P (Silmaril.Wasm.SingleThreaded.profile o)).invoke a []) cs c')
    {ys : List Flat}
    (hf : (core3P (Silmaril.Wasm.SingleThreaded.profile o)).status c'.1 c'.2 =
      .returned (.values ys))
    (p : List (Move (sigN (CoreModule.imports cm).length) (sigN (CoreModule.exports cm).length))) :
    instPlay (F := sigN (CoreModule.exports cm).length) cs .ready ++ p.map liftMove ∈
        (coreModSemI (Silmaril.Wasm.SingleThreaded.profile o)).sem cm ↔
      p ∈ engineStrategy (core3P (Silmaril.Wasm.SingleThreaded.profile o)) ⟨c'.1, J.addrs⟩
        (CoreModule.imports cm) (CoreModule.exports cm) :=
  core3_after_start_iff hJ ha hr hf p

end Silmaril.Wasm.Component.Binary
