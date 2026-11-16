module

public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Wasm.Abstract.HostSquareXP.Defs
public import Silmaril.Wasm.Abstract.HostStrat.Defs
public import Silmaril.Games.Abstract.StratHost.Defs
public import Silmaril.Games.Abstract.StratSession.Defs

/-!
# Sessions of invocations with exceptions against a host: definitions

`Silmaril.Wasm.Abstract.HostStrat` threads the store-retaining Core triple `coreTripleS`, which
has no finished end for an uncaught exception (Core 3.0 observations `CoreObsL`). This module
gives the exception-aware session triples, on both sides of the square, at one fixed host:

* `CoreBehSXP`, `coreTripleSXP P host Ok`: the Core triple with exceptions
  (`obsTriple Ok (CoreObsLXP …)`), except that a trap round keeps the store of the Core trap
  configuration `⟨s₂, {}, [.trap]⟩`, as the answer `.ret (.inr ()) s₂`. Values are
  `.ret (.inl (.inl ws)) s₂`, an uncaught exception `t` is `.ret (.inl (.inr t)) s₂` (the Core run
  to `throwing t`), and there is no plain `End.trap`;
* `coreSessionXP P host Ok s₀`: its session threading (`StratSession.threadS`) from `s₀`;
* `natTripleSXP host Ok`: the native session triple `sessionTripleXP` (the closure with
  store-keeping traps, `HostClosingS`) at the questions `Ok`, restricted by the host
  (`StratHost.hostRestrict (coreHostRel host)`). This is the construction of
  `obsTriple_natXP_eq` (`OpenStrat`) on the session triple;
* `natSessionXP host Ok s₀`: its session threading from `s₀`.

Theorems in `Silmaril.Wasm.Abstract.HostSessionXP.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The Core behaviours with exceptions of one invocation with the store of a trap kept: values
or an uncaught exception at their store, a trap configuration with its store
(`.ret (.inr ()) s₂`), or host-free divergence. A plain `End.trap` is no behaviour. -/
def CoreBehSXP (P : Numerics.Profile) (host : HostSemantics H) (s : Store H)
    (q : Nat × List Val) : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit) → Prop
  | (cs, .ret (.inl r) s₂) => CoreObsLXP P host s q.1 q.2 (.done cs (.ret r s₂))
  | (cs, .ret (.inr _) s₂) => EvRun P host (invoke s q.1 q.2) cs ⟨s₂, {}, [.trap]⟩
  | (_, .trap) => False
  | (cs, .div) => CoreObsLXP P host s q.1 q.2 (.div cs)

/-- **The store-retaining Core triple with exceptions** on the questions `Ok`: as
`obsTriple Ok (fun s q => CoreObsLXP P host s q.1 q.2)`, except that a trap round keeps the store
of the Core trap configuration. -/
def coreTripleSXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit) :=
  (fun s q => {x | Ok s q ∧ CoreBehSXP P host s q x},
    fun s q => {x | Ok s q ∧
      (CoreObsLXP P host s q.1 q.2 (.blocked x.1 x.2) ∨
        CoreObsLXP P host s q.1 q.2 (.hostDiv x.1 x.2))},
    fun s q => {ω | Ok s q ∧ CoreObsLXP P host s q.1 q.2 (.prod ω)})

/-- **The Core session with exceptions** from the store `s₀`: the store is threaded through
returns, uncaught exceptions and traps. -/
def coreSessionXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) (s₀ : Store H) :
    DStrategy (wasmHostSig H) (sig1 (Nat × List Val) (List Val ⊕ Nat)) :=
  StratSession.threadS (coreTripleSXP P host Ok) s₀

/-- **The native session triple against `host`** on the questions `Ok`: the session triple with
store-keeping traps, restricted by the host. -/
def natTripleSXP (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) ((List Val ⊕ Nat) ⊕ PUnit) :=
  StratHost.hostRestrict (coreHostRel host) (StratHost.guardT Ok sessionTripleXP)

/-- **The native session with exceptions** against `host` from the store `s₀`. -/
def natSessionXP (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop)
    (s₀ : Store H) : DStrategy (wasmHostSig H) (sig1 (Nat × List Val) (List Val ⊕ Nat)) :=
  StratSession.threadS (natTripleSXP host Ok) s₀

end Silmaril.Wasm.Abstract
