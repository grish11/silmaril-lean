module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore.Main
public import Silmaril.Proofs.Wasm.Component.InstTests.Transfer
public import Silmaril.Proofs.Wasm.Component.InstLitmus.Pos
public import Silmaril.Proofs.Wasm.Component.InstSem.Run
public import Silmaril.Wasm.Component.InstWired.Thms

/-!
# `trap.wasm` from the first-core theorem

* `failRefWired_of_rest`: `Task.failRefWired` from its remaining cases `Task.failRefWiredRest`
  (the case `k = 0` in the first-core fragment is `firstCore_fail_ref`);
* `trapCM_nodeQuiet`: the first core node of the IR reading of `trap.wasm` (the module `trap`,
no wiring) fails quietly: its start function traps (`InstLitmus.trapMod_inst`, transferred to
the lowered module by `InstTests.sem_trap`, then `coreNodeI_engine_nil`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstLitmus Silmaril.Wasm.Component.InstTests
open Silmaril.Wasm.SingleThreaded (profile neverFail)
open Silmaril.Proofs.Wasm.Component.InstSem

/-- **The first node of `trap.wasm` fails quietly.** -/
theorem trapCM_nodeQuiet : NodeQuiet hostI.length (.fail ()) trapCM [] := by
  have hS : (instRound (F := CoreIface.sig (CoreModule.exports trapCM))
      (([] : List (Round sigU (CoreIface.sig (CoreModule.imports trapCM)))).map Round.call)
      (InstAns.fail ())).moves ∈ (Binary.coreModSemI (profile neverFail)).sem trapCM := by
    rw [Silmaril.Proofs.Wasm.Component.InstTests.sem_trap]
    exact Silmaril.Proofs.Wasm.Component.InstLitmus.trapMod_inst _
  have h := Silmaril.Proofs.Wasm.Component.InstSem.coreNodeI_inst
    (Binary.coreModSemI (profile neverFail)) hostI.length trapCM [] [] (InstAns.fail ()) hS
    (by simp)
  rw [← Silmaril.Proofs.Wasm.Component.InstSem.instPlay_eq] at h
  exact coreNodeI_engine_nil h

open Silmaril.Wasm.Component.Conformance in
/-- **`Task.failRefWired` from its remaining cases.** -/
theorem failRefWired_of_rest (h : Task.failRefWiredRest) : Task.failRefWired := by
  intro b c r ps k hk hc hr hv hw himp hn hready hfail
  by_cases hk0 : k = 0
  · by_cases hf : FirstCoreFrag r
    · subst hk0
      exact firstCore_fail_ref hc hr hw hf hn hk hfail
    · exact h b c r ps k hk (.inr hf) hc hr hv hw himp hn hready hfail
  · exact h b c r ps k hk (.inl (Nat.pos_of_ne_zero hk0)) hc hr hv hw himp hn hready hfail

end Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
