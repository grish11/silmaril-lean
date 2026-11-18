module

public import Silmaril.Wasm.Cfg.ExampleHostExn.Defs
public import Silmaril.Wasm.Cfg.CfgValid.Thms
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Games.Abstract.StratSession.Defs
import Silmaril.Proofs.Wasm.Cfg.ExampleHostExn
import Silmaril.Proofs.Wasm.Cfg.ExampleHostExnRun

@[expose] public section

/-!
# Host exceptions and traps under `try_table`, on the self-contained CFG closure

Fixtures on one validated store, stated against the self-contained CFG session triple
`CfgClosure.cfgSessionTripleC` (finished `cfgEvFunDXPSC`, pending `CfgSession.cfgEvPendXPS`) and its
sessions `StratSession.threadS cfgSessionTripleC hxStore`. They are **proved on the CFG closure
directly**: each activation is an explicit run of the logged machine (`MachineL.MRunL`, `ReachL`,
`TailL`), resolved by `Shape.close` of the CFG open module `CfgSession.cfgHOpenXPS`. Only
`exn_session_native` goes through `CfgClosure.cfgSessionTripleC_eq`.

In the session semantics a call to the host `h` is one open host call `hostAns s r s'`, its answer
any result `r` (values, `.throw t`, `.trap`) and store `s'`. A host answer `.throw t` is an
exception raised at the call site; a pending tail call to `h` is made when the caller's frame is
left, outside its handlers; a host trap is a trap, never an exception.

**Validation.** `hxMod` validates (`hx_valid`), `hxI` is its spec instance against a fresh host
function (`hx_specInstance`), so `hxStore` is valid (`hx_storeOk`); the exception checker accepts
it (`hx_chk`, by `storeChkEB`).

**1. Pending calls: handler versus tail.** `callH_pending`, `tailH_pending`: in both `callH`
(`try_table (catch 0 0) (call 0)`) and `tailH` (`try_table (catch 0 0) (return_call 0)`) the
host call `h()` at `hxStore` is a pending call of `cfgEvPendXPS`, with the empty log before it.
The observations are equal; the machine shows where each call is made. `callH_pending_machine`:
the call is reached (`ReachL`) inside the arm, the `try_table`'s handler frame (`tryT`, clauses
`[catchE]`) on the label stack, so the handler is active at the call. `tailH_pending_machine`:
the body ends in the pending tail call `(hxStore, _, .tail 0 [] 1)` (`TailL`), made when the frame
is left. Fixtures 2 and 3 show the difference when the host answers with an exception.
`pend_session`: after a completed `callH` round, `tailH` is pending at `h()` in the store that
round left.

**2. Caught host throw.** `callH_caught`: the host allocates the exception `hxExn v` of `$e`
(address `0`, payload `v`) and throws it (`.throw 0`, leaving `hxThrown v`); `catch 0 0` catches
it and `callH` returns `[v]` in `hxThrown v`, its log that one host call.
`callH_caught_existing`: the same from `hxThrown v`, the host throwing the existing exception.

**3. Tail host throw bypasses the handler.** `tailH_uncaught`, `tailH_uncaught_existing`: the
same host answers reached through `return_call` are not caught by the same clause: `tailH` ends
with the uncaught exception `.ret (.inl (.inr 0)) (hxThrown v)`, keeping the host's store.
`exn_session`: the session play `callH` (caught, `42`) then `tailH` (uncaught exception `0`).

**4. A host trap is not caught.** `trapH_trap`: in `trapH` (`try_table (catch_all 0) (call 0;
drop)`), a host answer `.trap` leaving any `s'` makes `trapH` trap, `.ret (.inr ()) s'`, keeping
`s'`; `trapH_caught`: the same `catch_all` does catch a host exception (`trapH` returns no values).
`trap_session`: `trapH` traps with the host leaving `hxThrown 42`; the session continues from that
store, where `callH` catches the host's rethrow of the existing exception and returns `42`.

**Scope.** The host's answers are chosen among those the session allows; the theorems exhibit
these behaviours (membership), they do not characterise all behaviours. `hxThrown v` is the
store the host answers with; its validity is not proved here.
-/

namespace Silmaril.Wasm.Cfg.ExampleHostExn

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL Silmaril.Wasm.Cfg.CfgSession
  Silmaril.Wasm.Cfg.CfgClosure
open Silmaril.Wasm.Interp (StoreChkE ehExt)
open Silmaril.Games.Abstract.StratSession (threadS sroundsMoves sroundMoves)

/-! ## Validation -/

/-- **`hxMod` validates.** -/
theorem hx_valid : validate? hxMod = some hxMT := Proofs.ExampleHostExn.hx_valid

/-- **`hxI` is the spec instance of `hxMod`** against a fresh host function. -/
theorem hx_specInstance : IsSpecInstance hxMod hxMT hxI hxC₀ :=
  Proofs.ExampleHostExn.hx_specInstance

/-- **The store is valid.** -/
theorem hx_storeOk : StoreOk hxStore := Proofs.ExampleHostExn.hx_storeOk

/-- **The exception checker accepts the store.** -/
theorem hx_chk : StoreChkE (ehExt hxStore.tags) hxStore.funcs := Proofs.ExampleHostExn.hx_chk

/-! ## 1. Pending calls: handler versus tail -/

/-- **`callH` is pending at `h()`**, with the empty log before it. -/
theorem callH_pending :
    (([] : List (Call (Abstract.wasmHostSig Nat))), ((0 : Nat), hxStore, ([] : List Val))) ∈
      cfgSessionTripleC.2.1 hxStore (1, []) :=
  Proofs.ExampleHostExn.callH_pend rfl

/-- **`tailH` is pending at `h()`**, with the empty log before it. -/
theorem tailH_pending :
    (([] : List (Call (Abstract.wasmHostSig Nat))), ((0 : Nat), hxStore, ([] : List Val))) ∈
      cfgSessionTripleC.2.1 hxStore (2, []) :=
  Proofs.ExampleHostExn.tailH_pend rfl

/-- **`callH`'s pending call is made inside the handler**: the machine enters the `try_table`,
pushing its handler frame (clauses `[catchE]`), and the arm reaches the call `h()`. -/
theorem callH_pending_machine :
    MRunL callBody (initial callBody hxStore (Frame.forCall hxMI [] [])) []
        ⟨.block ⟨[(0, 0)], 0⟩, [], [⟨1, [], false, true, [catchE], .value .i32⟩], hxStore,
          Frame.forCall hxMI [] []⟩ ∧
      ReachL callBody ⟨.block ⟨[(0, 0)], 0⟩, [], [⟨1, [], false, true, [catchE], .value .i32⟩],
        hxStore, Frame.forCall hxMI [] []⟩ [] ⟨0, ([], hxStore)⟩ :=
  Proofs.ExampleHostExn.callH_pend_machine

/-- **`tailH`'s pending call is a tail call**: from the same handler frame, the body ends in the
pending tail call to `h` (result arity `1`), made when the frame is left. -/
theorem tailH_pending_machine :
    MRunL tailBody (initial tailBody hxStore (Frame.forCall hxMI [] [])) []
        ⟨.block ⟨[(0, 0)], 0⟩, [], [⟨1, [], false, true, [catchE], .value .i32⟩], hxStore,
          Frame.forCall hxMI [] []⟩ ∧
      TailL tailBody ⟨.block ⟨[(0, 0)], 0⟩, [], [⟨1, [], false, true, [catchE], .value .i32⟩],
        hxStore, Frame.forCall hxMI [] []⟩ [] (hxStore, Frame.forCall hxMI [] [], .tail 0 [] 1) :=
  Proofs.ExampleHostExn.tailH_pend_machine

/-- **`tailH` pending after a caught round**: `callH` catches the host's exception and returns
`42`; then `tailH` is pending at `h()` in the store the host left. -/
theorem pend_session :
    sroundsMoves [((1, []), [hostAns hxStore (.throw 0) (hxThrown 42)], .inl (.inl [.i32 42]))] ++
        .inr (.ask (2, [])) :: [.inl (.ask ((0 : Nat), hxThrown 42, []))] ∈
      (threadS cfgSessionTripleC hxStore).toStrategy :=
  Proofs.ExampleHostExn.pend_session

/-! ## 2. Caught host throw -/

/-- **A host exception caught by `catch 0 0`**: the host allocates `hxExn v` and throws it;
`callH` returns its payload `v`, in the host's store. -/
theorem callH_caught (v : BitVec 32) :
    ([hostAns hxStore (.throw 0) (hxThrown v)], End.ret (.inl (.inl [.i32 v])) (hxThrown v)) ∈
      cfgSessionTripleC.1 hxStore (1, []) :=
  Proofs.ExampleHostExn.callH_round v

/-- The same, the host rethrowing the existing exception `hxExn v`. -/
theorem callH_caught_existing (v : BitVec 32) :
    ([hostAns (hxThrown v) (.throw 0) (hxThrown v)], End.ret (.inl (.inl [.i32 v])) (hxThrown v)) ∈
      cfgSessionTripleC.1 (hxThrown v) (1, []) :=
  Proofs.ExampleHostExn.callH_round_existing v

/-! ## 3. Tail host throw bypasses the handler -/

/-- **The same host exception through `return_call` is not caught**: `tailH` ends with the
uncaught exception `0`, in the host's store. -/
theorem tailH_uncaught (v : BitVec 32) :
    ([hostAns hxStore (.throw 0) (hxThrown v)], End.ret (.inl (.inr 0)) (hxThrown v)) ∈
      cfgSessionTripleC.1 hxStore (2, []) :=
  Proofs.ExampleHostExn.tailH_round v

/-- The same, the host rethrowing the existing exception `hxExn v`, which `callH` catches
(`callH_caught_existing`). -/
theorem tailH_uncaught_existing (v : BitVec 32) :
    ([hostAns (hxThrown v) (.throw 0) (hxThrown v)], End.ret (.inl (.inr 0)) (hxThrown v)) ∈
      cfgSessionTripleC.1 (hxThrown v) (2, []) :=
  Proofs.ExampleHostExn.tailH_round_existing v

/-- **Caught, then uncaught, in one session**: `callH` returns `42`; then `tailH`, the host
rethrowing the same exception, ends with the uncaught exception `0`. -/
theorem exn_session :
    sroundsMoves [((1, []), [hostAns hxStore (.throw 0) (hxThrown 42)], .inl (.inl [.i32 42])),
        ((2, []), [hostAns (hxThrown 42) (.throw 0) (hxThrown 42)], .inl (.inr 0))] ∈
      (threadS cfgSessionTripleC hxStore).toStrategy :=
  Proofs.ExampleHostExn.exn_session

/-! ## 4. A host trap is not caught -/

/-- **A host trap under `catch_all`**: `trapH` traps, keeping the host's store. -/
theorem trapH_trap (s' : Store Nat) :
    ([hostAns hxStore .trap s'], End.ret (.inr ()) s') ∈ cfgSessionTripleC.1 hxStore (3, []) :=
  Proofs.ExampleHostExn.trapH_round s'

/-- The same `catch_all` catches any host exception: `trapH` returns no values. -/
theorem trapH_caught (t : Nat) (s' : Store Nat) :
    ([hostAns hxStore (.throw t) s'], End.ret (.inl (.inl [])) s') ∈
      cfgSessionTripleC.1 hxStore (3, []) :=
  Proofs.ExampleHostExn.trapH_round_throw t s'

/-- **Trap then resume**: `trapH` traps with the host leaving `hxThrown 42`; the session continues
from that store, where `callH` catches the host's rethrow of the existing exception. -/
theorem trap_session :
    sroundMoves ((3, []), [hostAns hxStore .trap (hxThrown 42)], .inr PUnit.unit) ++
        sroundMoves ((1, []), [hostAns (hxThrown 42) (.throw 0) (hxThrown 42)],
          .inl (.inl [.i32 42])) ∈
      (threadS cfgSessionTripleC hxStore).toStrategy :=
  Proofs.ExampleHostExn.trap_session

/-! ## The native session triple, through `cfgSessionTripleC_eq` -/

/-- Caught, then uncaught, in the native session (`Abstract.sessionTripleXP`). -/
theorem exn_session_native :
    sroundsMoves [((1, []), [hostAns hxStore (.throw 0) (hxThrown 42)], .inl (.inl [.i32 42])),
        ((2, []), [hostAns (hxThrown 42) (.throw 0) (hxThrown 42)], .inl (.inr 0))] ∈
      (threadS Abstract.sessionTripleXP hxStore).toStrategy := by
  rw [← cfgSessionTripleC_eq]; exact exn_session

end Silmaril.Wasm.Cfg.ExampleHostExn
