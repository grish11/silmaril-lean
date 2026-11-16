module

public import Silmaril.Wasm.Abstract.HostSquareXP.Defs
public import Silmaril.Wasm.Abstract.HostStrat.Defs
public import Silmaril.Wasm.Interp.HostEvalP.Thms

/-!
# Invocations with exceptions against a host as canonical strategies: definitions

The canonical-relation analogue of `Silmaril.Wasm.Abstract.HostStrat`: the exact-log observations
with exceptions, native (`NatObsXP`) and Core (`CoreObsLXP`), sent to the canonical play object by
the same `obsTriple` and `atTriple`. An uncaught exception `t` is the answer `.inl (.inr t, s₂)`
(final store hidden in the per-function strategies); a trap is `.inr ()`.

* `InvOkXP tags`: a checked store with the tag invariants, checked under the exception extension,
  and a typed invocation (the hypotheses of `hostSquareXP_done`);
* `natStratXP host Ok`, `coreStratXP P host Ok`: all invocations;
* `natStratAtXP host Ok s a`, `coreStratAtXP P host Ok s a`: the one function at `a` in `s`.

Theorems in `Silmaril.Wasm.Abstract.HostStratXP.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (TagsOk StoreChkE ehExt)

variable {H : Type}

/-- A checked store with the tag invariants, checked under the exception extension, and a typed
invocation. -/
def InvOkXP (tags : List TagInst) (s : Store H) (q : Nat × List Val) : Prop :=
  StoreOk s ∧ StoreChkE (ehExt tags) s.funcs ∧ TagsOk tags s ∧ InvokeOk s q.1 q.2

/-- **The native strategy with exceptions** of invocations against `host`, on the questions
`Ok`. -/
def natStratXP (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) :
    DStrategy (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)) :=
  StratObs.toDStrat (obsTriple Ok fun s q => NatObsXP host s q.1 q.2)

/-- **The Core strategy with exceptions** of invocations against `host` at the profile `P`, on
the questions `Ok`. -/
def coreStratXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    DStrategy (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)) :=
  StratObs.toDStrat (obsTriple Ok fun s q => CoreObsLXP P host s q.1 q.2)

/-- The native strategy with exceptions of the function at `a` in `s`, final store hidden. -/
def natStratAtXP (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) (s : Store H)
    (a : Nat) : DStrategy (wasmHostSig H) (funSig Unit (List Val) (List Val ⊕ Nat)) :=
  StratObs.toDStrat (atTriple (obsTriple Ok fun s q => NatObsXP host s q.1 q.2) s a)

/-- The Core strategy with exceptions of the function at `a` in `s`, final store hidden. -/
def coreStratAtXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) (s : Store H) (a : Nat) :
    DStrategy (wasmHostSig H) (funSig Unit (List Val) (List Val ⊕ Nat)) :=
  StratObs.toDStrat (atTriple (obsTriple Ok fun s q => CoreObsLXP P host s q.1 q.2) s a)

end Silmaril.Wasm.Abstract
