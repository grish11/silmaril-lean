module

public import Silmaril.Wasm.Abstract.HostSquare.Defs
public import Silmaril.Games.Abstract.StratObs.Defs

/-!
# Invocations against a host as canonical strategies: definitions

The exact-log observations of an invocation against a Core 3.0 host (`FullObs`) are sent to the
canonical play object `DStrategy` (`Silmaril.Games.Abstract.StratObs`), on the native side
(`NatObs`) and on the Core side (`CoreObsL`).

**The interface.** A question is a store `s` with a function address and arguments `(a, vs)`;
an answer is a return with its final store, or a trap without payload. The import interface is
the host signature `wasmHostSig H`: Proponent calls a host function, Opponent answers.

**The triple** `obsTriple Ok O` of a family `O s q : FullObs H → Prop` of observations,
restricted to the questions with `Ok s q` (other questions get no behaviour):

* finished behaviours: the `done` observations, and the host-free divergences `div` as
  behaviours ending in `.div`;
* pending calls: the `blocked` and the `hostDiv` observations. Both are a host call that is never
  answered; the strategy does not tell a host without outcome from a host that diverges;
* productive runs: the `prod` observations.

The plays of the strategy are only the host-consistent logs: this is the closed interaction with
the fixed host, read as a strategy on the host interface. The domains:

* `InvOk`: a checked store and a typed invocation (`hostSquare`);
* `InvOkN`: moreover, the store's Wasm functions are native-profile code (`hostSquare_profile`).

Theorems in `Silmaril.Wasm.Abstract.HostStrat.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The observation triple** of a family of exact-log observations, on the questions `Ok`. -/
def obsTriple (Ok : Store H → Nat × List Val → Prop)
    (O : Store H → Nat × List Val → FullObs H → Prop) :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  (fun s q => {x | Ok s q ∧ (O s q (.done x.1 x.2) ∨ (x.2 = .div ∧ O s q (.div x.1)))},
    fun s q => {x | Ok s q ∧ (O s q (.blocked x.1 x.2) ∨ O s q (.hostDiv x.1 x.2))},
    fun s q => {ω | Ok s q ∧ O s q (.prod ω)})

/-- A checked store and a typed invocation. -/
def InvOk (s : Store H) (q : Nat × List Val) : Prop :=
  StoreOk s ∧ Interp.StoreChk s.funcs ∧ InvokeOk s q.1 q.2

/-- `InvOk`, with native-profile Wasm functions in the store. -/
def InvOkN (s : Store H) (q : Nat × List Val) : Prop :=
  InvOk s q ∧ Interp.NativeWasmFuncs s.funcs

/-- **The native strategy** of invocations against `host` on the questions `Ok`. -/
def natStrat (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) :
    DStrategy (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)) :=
  StratObs.toDStrat (obsTriple Ok fun s q => NatObs host s q.1 q.2)

/-- **The Core strategy** of invocations against `host` at the profile `P`, on the questions
`Ok`. -/
def coreStrat (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    DStrategy (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)) :=
  StratObs.toDStrat (obsTriple Ok fun s q => CoreObsL P host s q.1 q.2)

end Silmaril.Wasm.Abstract
