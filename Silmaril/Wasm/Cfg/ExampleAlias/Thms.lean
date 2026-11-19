module

public import Silmaril.Wasm.Cfg.ExampleAlias.Defs
public import Silmaril.Wasm.Cfg.DanglingExn.Thms
public import Silmaril.Wasm.Cfg.DanglingTyped.Thms
public import Silmaril.Wasm.Cfg.CfgClosure.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Interp.CheckComplete.Defs
import Silmaril.Proofs.Wasm.Cfg.ExampleAlias
import Silmaril.Proofs.Wasm.Cfg.ExampleAliasRun

@[expose] public section

/-!
# A validated aliasing cycle through a dangling host exception (theorems)

**Validation.** `alI` is the spec instance of `alMod` (`al_specInstance`); its store is `StoreOk`,
accepted by the exception checker (`al_chk`, by `storeChkEB`), in the checker's instruction
profile (`al_supported`), hence in the explicit domain (`al_instDom`) with supported functions
(`al_funcsSupp`) and `StoreOkD`.

**The run.** With `h()` answered by the dangling exception `0` (`al_instHostU_throw`, an answer of
the unrestricted universal host `instHostU alI`):

* natively, on the CFG session triple (`run_round`): `grab`'s `catch_all_ref 0` catches the
  exception with `ref.exn 0` as payload, `run` throws `$t` with it, allocating
  `alCyc = ⟨0, [ref.exn 0]⟩` at address `0`, and ends with the uncaught exception `0` in `alEnd`;
* in Core (`run_core_U`, every profile): the same host event, the same end (`throwing 0` in
  `alEnd`). Obtained from the native round by `DanglingExn.fin_sub` (native ⊆ Core);
* the allocation itself, in both semantics (`run_throw_core`, `run_throw_native`: the
  instances of `DanglingExn.step_throw_self` and `evalLXPh_throw_self` at `alStore`).

**The end store.** `alEnd` is not `StoreOk` (`alEnd_not_storeOk`: its exception reaches itself,
`acyclicExns`), but it is `StoreOkD` (`alEnd_storeOkD`: the relaxed invariant carried along the
Core run by `ConfigOkD.evRun` at `hostTypedD_instHostU`).

**Checker acceptance does not give `FuncsSupp`.** `dcI` (`dcMod`) is in the explicit domain
`CfgInst.InstDom` (`dc_instDom`), but its function holds a dead `ref.test`, which the checker skips
after `unreachable`: `dc_not_funcsSupp`, `dc_not_supported`. The relaxed invariant's entry domain
is therefore stated with `CheckComplete.StoreSupported` (`DanglingTyped.configOkD_of_supported`).
-/

namespace Silmaril.Wasm.Cfg.ExampleAlias

open Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Wasm.Cfg.DanglingTyped (FuncsSupp StoreOkD)

variable {P : Numerics.Profile}

/-! ## Validation -/

/-- **`alI` is the spec instance of `alMod` against a fresh host function.** -/
theorem al_specInstance : IsSpecInstance alMod alMT alI alC₀ :=
  Proofs.ExampleAlias.al_specInstance

theorem al_storeOk : StoreOk alStore := Proofs.ExampleAlias.al_storeOk

/-- The exception checker accepts the store. -/
theorem al_chk : StoreChkE (ehExt alStore.tags) alStore.funcs := Proofs.ExampleAlias.al_chk

/-- The store is in the checker's instruction profile. -/
theorem al_supported : Interp.CheckComplete.StoreSupported alStore.funcs :=
  Proofs.ExampleAlias.al_supported

theorem al_instDom : CfgInst.InstDom alI alStore := Proofs.ExampleAlias.al_instDom

theorem al_funcsSupp : FuncsSupp alStore := Proofs.ExampleAlias.al_funcsSupp

theorem al_storeOkD : StoreOkD alStore :=
  DanglingTyped.storeOkD_of_storeOk al_storeOk al_funcsSupp

/-! ## The run -/

/-- Address `0` is dangling in `alStore`. -/
theorem al_dangling : DanglingExn.Dangling alStore 0 := Nat.le_refl 0

/-- **The unrestricted universal host of `alI` answers `h()` by the dangling exception `0`.** -/
theorem al_instHostU_throw :
    CfgInst.instHostU alI 0 alStore [] (.returned alStore (.throw 0)) :=
  Proofs.ExampleAlias.al_instHostU_throw

/-- **`run` on the CFG session triple**: the self-referencing exception `0`, uncaught, in
`alEnd`. -/
theorem run_round :
    ([alAns], End.ret (.inl (.inr 0)) alEnd) ∈ CfgClosure.cfgSessionTripleC.1 alStore (1, []) :=
  Proofs.ExampleAlias.run_round

/-- **The same round in Core**, at `instHostU alI`, every profile. -/
theorem run_core_U :
    Abstract.EvRun P (CfgInst.instHostU alI) (invoke alStore 1 []) [alAns]
      ⟨alEnd, {}, throwing 0⟩ :=
  Proofs.ExampleAlias.run_core_U

/-- **The allocation in Core**: `throw 0` with payload `ref.exn 0` allocates `alCyc` at `0`. -/
theorem run_throw_core {host : HostSemantics Nat} :
    Step P host ⟨alStore, alFr, [.ref (.exn 0), .plain (.throw ⟨0⟩)]⟩
      ⟨alEnd, alFr, throwing 0⟩ :=
  DanglingExn.step_throw_self (s := alStore) (f := alFr) (ta := 0) rfl (Expand.iff.2 rfl) rfl

/-- **The allocation natively**: the same store and exception. -/
theorem run_throw_native :
    Abstract.EvalLXPh alStore alFr [.ref (.exn 0)] [.op (.throw ⟨0⟩) []] []
      (alEnd, alFr, .flow (.throw 0)) :=
  DanglingExn.evalLXPh_throw_self (s := alStore) (f := alFr) (ta := 0) rfl (Expand.iff.2 rfl) rfl

/-! ## The end store -/

/-- **`alEnd` is not `StoreOk`**: its exception at `0` reaches itself. -/
theorem alEnd_not_storeOk : ¬ StoreOk alEnd :=
  DanglingExn.not_storeOk_addExn_self (s := alStore) 0

/-- **`alEnd` satisfies the relaxed store invariant.** -/
theorem alEnd_storeOkD : StoreOkD alEnd := Proofs.ExampleAlias.alEnd_storeOkD

/-! ## Checker acceptance without supported functions -/

/-- `dcI` is the spec instance of `dcMod`. -/
theorem dc_specInstance : IsSpecInstance dcMod dcMT dcI dcC₀ := Proofs.ExampleAlias.dc_specInstance

/-- **`dcStore` is in the explicit domain.** -/
theorem dc_instDom : CfgInst.InstDom dcI dcStore := Proofs.ExampleAlias.dc_instDom

/-- **`dcStore` does not have supported functions** (a dead `ref.test`). -/
theorem dc_not_funcsSupp : ¬ FuncsSupp dcStore := Proofs.ExampleAlias.dc_not_funcsSupp

/-- `dcStore` is not in the checker's instruction profile. -/
theorem dc_not_supported : ¬ Interp.CheckComplete.StoreSupported dcStore.funcs :=
  Proofs.ExampleAlias.dc_not_supported

end Silmaril.Wasm.Cfg.ExampleAlias
