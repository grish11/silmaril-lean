module

public import Silmaril.Wasm.Cfg.ExampleRegress.Defs
public import Silmaril.Wasm.Cfg.CfgValid.Thms
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Games.Abstract.StratSession.Defs
import Silmaril.Proofs.Wasm.Cfg.ExampleRegress
import Silmaril.Proofs.Wasm.Cfg.ExampleRegressRun

@[expose] public section

/-!
# Regression fixtures for the self-contained CFG closure

Three fixtures on one validated store, stated against the self-contained CFG session triple
`CfgClosure.cfgSessionTripleC` (every body run on the logged CFG machine, every internal call
answered by the CFG closure) and its sessions `StratSession.threadS cfgSessionTripleC rgStore`.
They are **proved on the CFG closure directly**: each activation is an explicit run of the logged
machine (`MachineL.MRunL`, `MachineL.ProdL`), resolved by `Shape.close`/`Shape.closeInfL` of the
CFG open modules (`CfgSession.cfgHOpenXPS`, `CfgSession.cfgHOpenXP`). Only the `_native`
corollaries go through `CfgClosure.cfgSessionTripleC_eq`, to the native session triple
`Abstract.sessionTripleXP`.

**Validation.** `rgMod` validates (`rg_valid`) and `rgI` is its spec instance against a fresh host
function (`rg_specInstance`), so `rgStore` is valid (`rg_storeOk`); the exception checker accepts
it (`rg_chk`, by `storeChkEB`), the remaining hypothesis of the `CfgValid` theorems.

**1. Recursion through a host** (`rec`, function `1`: `h(n)`, then `rec(n - 1)` when `n ≠ 0`).
`rec_run`: one activation of `rec (k + 1)` on the logged machine logs the host call `h(k + 1)` and
the internal call `rec k`, both open. `rec_log`: the CFG closure resolves the internal calls
recursively, so the finished behaviour of `rec k` has the host log `recLog rgStore k`, that is
`h(k), h(k - 1), …, h(0)`, one host call per recursion depth, and returns no values in
`rgStore` (for every `k < 2 ^ 32`; `rec_log_two` spells out `k = 2`). `rec_session`: it is a
completed round of the session.

**2. Trap then resume** (`trap`, function `2`, writes `42` to the global then traps; `get`,
function `3`, reads the global). `trap_round`: `trap` ends `.ret (.inr ()) rgStore42`, a trap that
keeps the written store. `get_round`: `get` at that store answers `42`; `get_fresh`: at the
original store it answers `0`. `trap_then_get`: the session play "ask `trap`, trap, ask `get`,
answer `42`": the trap's store is retained and the session continues from it.

**3. Productive host interaction** (`pump`, function `4`: a loop calling `h(k)` on a counter `k`,
forever). `pump_prod`: the logged machine runs `pump` forever, its log the stream of host calls on
`0, 1, 2, …` (`MachineL.ProdL`). `pump_stream`: the productive part of the CFG triple
(`CfgSession.cfgEvInfNXP`) has the exact stream `fun n => hostAt rgStore (BitVec.ofNat 32 n)`.
`pump_session`: it is an infinite play of the session. `regress_play`: after the two rounds of
fixture 2, the infinite `pump` play from the trap store, the host calls carrying `rgStore42`.

**Scope.** The host's answers are fixed to "no values, same store", one choice among the
answers the session closure allows; the theorems exhibit these behaviours (membership), they do
not characterise all behaviours.
-/

namespace Silmaril.Wasm.Cfg.ExampleRegress

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL Silmaril.Wasm.Cfg.CfgSession
  Silmaril.Wasm.Cfg.CfgClosure
open Silmaril.Wasm.Abstract (SCall)
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Games.Abstract.StratSession (threadS sroundsMoves)
open Silmaril.Games.Abstract.StratThread (streamPlay)

/-! ## Validation -/

/-- **`rgMod` validates.** -/
theorem rg_valid : validate? rgMod = some rgMT := Proofs.ExampleRegress.rg_valid

/-- **`rgI` is the spec instance of `rgMod`** against a fresh host function. -/
theorem rg_specInstance : IsSpecInstance rgMod rgMT rgI rgC₀ :=
  Proofs.ExampleRegress.rg_specInstance

/-- **The store is valid.** -/
theorem rg_storeOk : StoreOk rgStore := Proofs.ExampleRegress.rg_storeOk

/-- **The exception checker accepts the store.** -/
theorem rg_chk : StoreChkE (ehExt rgStore.tags) rgStore.funcs := Proofs.ExampleRegress.rg_chk

/-! ## 1. Recursion through a host -/

/-- **One activation of `rec (k + 1)` on the logged machine**: the host call `h(k + 1)` and the
recursive internal call `rec k`, both logged open, then the exit. -/
theorem rec_run (k : Nat) (hk : k + 1 < 2 ^ 32) :
    MRunL recBody (initial recBody rgStore (Frame.forCall rgMI [.i32 (BitVec.ofNat 32 (k + 1))] []))
      [SCall.mk 0 [.i32 (BitVec.ofNat 32 (k + 1))] rgStore (.inl (.inl [])) rgStore,
        SCall.mk 1 [.i32 (BitVec.ofNat 32 k)] rgStore (.inl (.inl [])) rgStore]
      ⟨.exit, [], [], rgStore, Frame.forCall rgMI [.i32 (BitVec.ofNat 32 (k + 1))] []⟩ :=
  Proofs.ExampleRegress.rec_run rfl k hk

/-- **Recursion through a host, resolved by the CFG closure**: `rec k` makes the host calls
`h(k), h(k - 1), …, h(0)` (`recLog`), one per recursion depth, and returns no values. -/
theorem rec_log (k : Nat) (hk : k < 2 ^ 32) :
    (recLog rgStore k, End.ret (.inl (.inl [])) rgStore) ∈
      cfgSessionTripleC.1 rgStore (1, [.i32 (BitVec.ofNat 32 k)]) :=
  Proofs.ExampleRegress.rec_log k hk

/-- **`rec 2`**: the host calls `h(2), h(1), h(0)`, at depths `0`, `1`, `2`. -/
theorem rec_log_two :
    ([hostAt rgStore 2, hostAt rgStore 1, hostAt rgStore 0], End.ret (.inl (.inl [])) rgStore) ∈
      cfgSessionTripleC.1 rgStore (1, [.i32 2]) :=
  rec_log 2 (by decide)

/-- **`rec k` is a completed round of the CFG session.** -/
theorem rec_session (k : Nat) (hk : k < 2 ^ 32) :
    sroundsMoves [((1, [.i32 (BitVec.ofNat 32 k)]), recLog rgStore k, .inl (.inl []))] ∈
      (threadS cfgSessionTripleC rgStore).toStrategy :=
  Proofs.ExampleRegress.rec_session k hk

/-! ## 2. Trap then resume -/

/-- **`trap` traps, keeping the store it wrote.** -/
theorem trap_round :
    (([] : List (Call (Abstract.wasmHostSig Nat))), End.ret (.inr ()) rgStore42) ∈
      cfgSessionTripleC.1 rgStore (2, []) :=
  Proofs.ExampleRegress.trap_round

/-- **`get` at the trap's store answers `42`.** -/
theorem get_round :
    (([] : List (Call (Abstract.wasmHostSig Nat))), End.ret (.inl (.inl [.i32 42])) rgStore42) ∈
      cfgSessionTripleC.1 rgStore42 (3, []) :=
  Proofs.ExampleRegress.get_round

/-- `get` at the original store answers `0`. -/
theorem get_fresh :
    (([] : List (Call (Abstract.wasmHostSig Nat))), End.ret (.inl (.inl [.i32 0])) rgStore) ∈
      cfgSessionTripleC.1 rgStore (3, []) :=
  Proofs.ExampleRegress.get_fresh

/-- **Trap then resume**: in the CFG session from `rgStore`, `trap` traps and the session
continues; `get` then answers `42`, the value `trap` wrote before trapping. -/
theorem trap_then_get :
    ([.inr (.ask (2, [])), .inr (.ans (2, []) (.inr PUnit.unit)), .inr (.ask (3, [])),
        .inr (.ans (3, []) (.inl (.inl [.i32 42])))] :
        List (Move (Abstract.wasmHostSig Nat) (sig1 (Nat × List Val) (List Val ⊕ Nat)))) ∈
      (threadS cfgSessionTripleC rgStore).toStrategy :=
  Proofs.ExampleRegress.trap_then_get

/-! ## 3. Productive host interaction -/

/-- **`pump` runs forever on the logged machine**, logging the host calls on `0, 1, 2, …`. -/
theorem pump_prod :
    ProdL pumpBody (initial pumpBody rgStore (Frame.forCall rgMI [] [.i32]))
      (fun n => SCall.mk 0 [.i32 (BitVec.ofNat 32 n)] rgStore (.inl (.inl [])) rgStore) :=
  Proofs.ExampleRegress.pump_prod rfl

/-- **`pump`'s productive stream in the CFG triple**: exactly the host calls `h(0), h(1), …`. -/
theorem pump_stream :
    (fun n => hostAt rgStore (BitVec.ofNat 32 n)) ∈ cfgSessionTripleC.2.2 rgStore (4, []) :=
  Proofs.ExampleRegress.pump_inf rfl

/-- **`pump` is an infinite play of the CFG session.** -/
theorem pump_session :
    streamPlay [] (4, []) (fun n => hostAt rgStore (BitVec.ofNat 32 n)) ∈
      (threadS cfgSessionTripleC rgStore).inf :=
  Proofs.ExampleRegress.pump_session

/-- **The three behaviours in one session**: `trap` (trap, store kept), `get` (`42`), then
`pump` forever from the trap's store. -/
theorem regress_play :
    streamPlay (sroundsMoves [((2, []), [], .inr PUnit.unit), ((3, []), [], .inl (.inl [.i32 42]))])
      (4, []) (fun n => hostAt rgStore42 (BitVec.ofNat 32 n)) ∈
      (threadS cfgSessionTripleC rgStore).inf :=
  Proofs.ExampleRegress.regress_play

/-! ## The native session triple, through `cfgSessionTripleC_eq` -/

/-- Trap then resume in the native session (`Abstract.sessionTripleXP`). -/
theorem trap_then_get_native :
    ([.inr (.ask (2, [])), .inr (.ans (2, []) (.inr PUnit.unit)), .inr (.ask (3, [])),
        .inr (.ans (3, []) (.inl (.inl [.i32 42])))] :
        List (Move (Abstract.wasmHostSig Nat) (sig1 (Nat × List Val) (List Val ⊕ Nat)))) ∈
      (threadS Abstract.sessionTripleXP rgStore).toStrategy := by
  rw [← cfgSessionTripleC_eq]; exact trap_then_get

/-- The three behaviours in one native session. -/
theorem regress_play_native :
    streamPlay (sroundsMoves [((2, []), [], .inr PUnit.unit), ((3, []), [], .inl (.inl [.i32 42]))])
      (4, []) (fun n => hostAt rgStore42 (BitVec.ofNat 32 n)) ∈
      (threadS Abstract.sessionTripleXP rgStore).inf := by
  rw [← cfgSessionTripleC_eq]; exact regress_play

/-- Recursion through a host in the native session closure. -/
theorem rec_log_native (k : Nat) (hk : k < 2 ^ 32) :
    (recLog rgStore k, End.ret (.inl (.inl [])) rgStore) ∈
      Abstract.sessionTripleXP.1 rgStore (1, [.i32 (BitVec.ofNat 32 k)]) := by
  rw [← cfgSessionTripleC_eq]; exact rec_log k hk

end Silmaril.Wasm.Cfg.ExampleRegress
