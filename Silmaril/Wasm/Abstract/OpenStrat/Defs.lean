module

public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingInf.Defs
public import Silmaril.Games.Abstract.StratObs.Defs

/-!
# The open, host-independent native strategy of invocations: definitions

`Silmaril.Wasm.Abstract.HostStrat` and `HostStratXP` send the observations of an invocation
against **one fixed host** to the canonical play object (`natStrat`, `natStratXP`). Those
observations (`NatObs`, `NatObsXP`) filter host-independent native components by the host
(`coreHostRel host`). This module takes the components themselves, before any filter:

* `openTripleXP`, with exceptions: finished behaviours with divergence `wasmEvFunDXP` (it
  contains the finished behaviours `wasmEvFunXP`: off `div` the two agree,
  `wasmEvFunDXP_of_ne_div`), pending host calls `wasmEvPendXP` and productive streams
  `wasmEvInfNXP`;
* `openTriple`, exception-free: `wasmEvFunD`, `wasmEvPend` and `wasmEvInfN`;
* `openStratXP`, `openStrat`: their play objects, on all questions. Opponent answers every host
  call with every `Store H × Result`.

No host semantics occurs. The fixed-host strategies are host restrictions of these
(`StratHost.hostRestrict`, theorems in `Silmaril.Wasm.Abstract.OpenStrat.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The open native triple with exceptions**: divergence-enabled finished behaviours, pending
host calls and productive streams, host-independent. -/
def openTripleXP : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  (wasmEvFunDXP, wasmEvPendXP, wasmEvInfNXP)

/-- **The open native strategy with exceptions.** -/
def openStratXP :
    DStrategy (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)) :=
  StratObs.toDStrat openTripleXP

/-- **The open native triple** (exception-free). -/
def openTriple : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  (wasmEvFunD, wasmEvPend, wasmEvInfN)

/-- **The open native strategy** (exception-free). -/
def openStrat :
    DStrategy (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)) :=
  StratObs.toDStrat openTriple

end Silmaril.Wasm.Abstract
