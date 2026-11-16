module

public import Silmaril.Wasm.Abstract.HostStrat.Defs

/-!
# The public interaction equivalence of an export: definitions

An export is a store `s` with a function address `a`. Its **public interaction** against a fixed
Core 3.0 host `host` at the profile `P` is what an invocation `invoke s a vs` shows through the
host-event runs (`EvRun`, `CoreInf`) of `Silmaril.Wasm.Abstract.HostCall`, with exactly the host
log it makes:

* finished ends after the log `cs`: values in the empty frame with the final store, or a trap;
* pending host callouts after `cs`: with no host outcome (`blocked`), or one the host diverges
  on;
* host-free divergence after `cs`;
* productive runs: infinitely many answered host calls (`CoreInf`).

**`PubEquiv P host Ok s a s' a'`** says two exports show the same of all this, for every
argument list `vs` and log `cs`, on the invocations admitted by `Ok` (`InvOk`: a checked store
and a typed invocation). It is stated from Core runs only, without strategies or denotations.
Internal Wasm calls are Core steps, not host events, so the internal call graph of an export is
invisible by construction: an export calling an internal helper and the export with the helper
inlined can be `PubEquiv`. The host log does show every store at a host callout and every store
the host answers with, and the final store, so `PubEquiv` is not a contextual equivalence over
stores; it is the equivalence of the exact-log public observations.

**The public strategy.** `pubTriple T s a` restricts an observation triple `T` of
`Silmaril.Wasm.Abstract.HostStrat` (questions: store, address and arguments) to the questions
`(s, (a, vs))`, indexed by the arguments `vs` alone, with the final store moved into the result
(`pubEnd`). `pubStrat P host Ok s a` is its canonical play object `StratObs.toDStrat` for the
Core triple of `coreStrat`, and `natPubStrat host Ok s a` the one for the native triple of
`natStrat`. Questions are argument lists; an answer is the result with the final store, or a
trap.

**Scope.** Native stores, no exceptions: a thrown tag never ends a Core run
(`coreStrat_not_mem_throw`). The exception-aware version (`CallXP`) waits for an
exception-aware `coreStrat`. This is not contextual full abstraction.

Theorems in `Silmaril.Wasm.Abstract.PubModule.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The configuration `c` is at the host callout `m`: the host call `m.1` with the arguments
`m.2.2` under some context, in the store `m.2.1`. -/
def AtCallout (c : Config H) (m : (wasmHostSig H).Op) : Prop :=
  ∃ (E : SingleThreaded.Ctx) (b : Nat),
    SingleThreaded.decompose? c.store c.code = some (E, b, m.1, m.2.2) ∧ c.store = m.2.1

/-- The host leaves the call `m` pending: it has no outcome, or it diverges. -/
def HostPends (host : HostSemantics H) (m : (wasmHostSig H).Op) : Prop :=
  (∀ o, ¬ host m.1 m.2.1 m.2.2 o) ∨ host m.1 m.2.1 m.2.2 .diverged

/-- **The public interaction equivalence** of two exports `(s, a)` and `(s', a')` against
`host` at the profile `P`, on the invocations admitted by `Ok`: for every argument list `vs` and
host log `cs`, the same values with final store, the same traps, the same blocked and
host-divergent callouts and the same host-free divergence at exactly `cs`, and the same
productive runs. -/
def PubEquiv (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) (s : Store H) (a : Nat) (s' : Store H) (a' : Nat) :
    Prop :=
  ∀ vs : List Val,
    (∀ (cs : List (Call (wasmHostSig H))) (ws : List Val) (s₂ : Store H),
      (Ok s (a, vs) ∧ EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩) ↔
        (Ok s' (a', vs) ∧ EvRun P host (invoke s' a' vs) cs ⟨s₂, {}, vals ws⟩)) ∧
    (∀ cs : List (Call (wasmHostSig H)),
      (Ok s (a, vs) ∧ ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩) ↔
        (Ok s' (a', vs) ∧ ∃ s₂, EvRun P host (invoke s' a' vs) cs ⟨s₂, {}, [.trap]⟩)) ∧
    (∀ (cs : List (Call (wasmHostSig H))) (hh : H) (s₁ : Store H) (us : List Val),
      (Ok s (a, vs) ∧ ∃ (c : Config H) (E : SingleThreaded.Ctx) (b : Nat),
          EvRun P host (invoke s a vs) cs c ∧
          SingleThreaded.decompose? c.store c.code = some (E, b, hh, us) ∧ c.store = s₁ ∧
          ∀ o, ¬ host hh s₁ us o) ↔
        (Ok s' (a', vs) ∧ ∃ (c : Config H) (E : SingleThreaded.Ctx) (b : Nat),
          EvRun P host (invoke s' a' vs) cs c ∧
          SingleThreaded.decompose? c.store c.code = some (E, b, hh, us) ∧ c.store = s₁ ∧
          ∀ o, ¬ host hh s₁ us o)) ∧
    (∀ (cs : List (Call (wasmHostSig H))) (hh : H) (s₁ : Store H) (us : List Val),
      (Ok s (a, vs) ∧ ∃ (c : Config H) (E : SingleThreaded.Ctx) (b : Nat),
          EvRun P host (invoke s a vs) cs c ∧
          SingleThreaded.decompose? c.store c.code = some (E, b, hh, us) ∧ c.store = s₁ ∧
          host hh s₁ us .diverged) ↔
        (Ok s' (a', vs) ∧ ∃ (c : Config H) (E : SingleThreaded.Ctx) (b : Nat),
          EvRun P host (invoke s' a' vs) cs c ∧
          SingleThreaded.decompose? c.store c.code = some (E, b, hh, us) ∧ c.store = s₁ ∧
          host hh s₁ us .diverged)) ∧
    (∀ cs : List (Call (wasmHostSig H)),
      (Ok s (a, vs) ∧ ∃ c : Config H, EvRun P host (invoke s a vs) cs c ∧
          Diverges P (fun _ _ _ _ => False) c) ↔
        (Ok s' (a', vs) ∧ ∃ c : Config H, EvRun P host (invoke s' a' vs) cs c ∧
          Diverges P (fun _ _ _ _ => False) c)) ∧
    ∀ ω : Nat → Call (wasmHostSig H),
      (Ok s (a, vs) ∧ CoreInf P host (invoke s a vs) ω) ↔
        (Ok s' (a', vs) ∧ CoreInf P host (invoke s' a' vs) ω)

/-- The end at the public interface: the final store moves into the result. -/
def pubEnd {S B : Type} : End S B → End PUnit (B × S)
  | .ret b s => .ret (b, s) PUnit.unit
  | .trap => .trap
  | .div => .div

/-- The public interface of an export: a question is an argument list; an answer is a result
with its final store, or a trap. -/
abbrev pubSig (H : Type) : Sig.{0} := funSig PUnit (List Val) ((List Val ⊕ Nat) × Store H)

/-- **The public triple** of the export `(s, a)`: the observations of `T` at the questions
`(s, (a, vs))`, indexed by `vs`. -/
def pubTriple (T : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat))
    (s : Store H) (a : Nat) :
    ObsTriple (wasmHostSig H) PUnit (List Val) ((List Val ⊕ Nat) × Store H) :=
  (fun _ vs => {x | ∃ e, (x.1, e) ∈ T.1 s (a, vs) ∧ pubEnd e = x.2},
    fun _ vs => T.2.1 s (a, vs),
    fun _ vs => T.2.2 s (a, vs))

/-- The Core observation triple underlying `coreStrat P host Ok`. -/
abbrev coreTriple (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  obsTriple Ok fun s q => CoreObsL P host s q.1 q.2

/-- **The public module strategy** of the export `(s, a)`, from Core runs. -/
def pubStrat (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) (s : Store H) (a : Nat) :
    DStrategy (wasmHostSig H) (pubSig H) :=
  StratObs.toDStrat (pubTriple (coreTriple P host Ok) s a)

/-- The public module strategy of the export `(s, a)`, from the native semantics. -/
def natPubStrat (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) (s : Store H)
    (a : Nat) : DStrategy (wasmHostSig H) (pubSig H) :=
  StratObs.toDStrat (pubTriple (obsTriple Ok fun s q => NatObs host s q.1 q.2) s a)

end Silmaril.Wasm.Abstract
