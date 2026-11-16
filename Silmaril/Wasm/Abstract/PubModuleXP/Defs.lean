module

public import Silmaril.Wasm.Abstract.PubModule.Defs
public import Silmaril.Wasm.Abstract.HostStratXP.Defs

/-!
# The public interaction equivalence of an export, with exceptions: definitions

The exception-aware analogue of `Silmaril.Wasm.Abstract.PubModule`, on the Core side only. An
export is a store `s` with a function address `a`; its public interaction against **one fixed**
Core 3.0 host `host` at the profile `P` is what an invocation `invoke s a vs` shows through the
host-event runs (`EvRun`, `CoreInf`) with exactly the host log it makes. As in `PubEquiv`, and
moreover:

* an **uncaught exception** is a finished end: a labelled run to the thrown exception
  `throwing t` (`REF.EXN_ADDR t; THROW_REF`) at the final store `s₂`, in the empty frame. This is
  the exact Core form of the exception end of `CoreObsLXP`.

**`PubEquivXP P host Ok s a s' a'`** says two exports show the same of all this, for every
argument list `vs` and log `cs`, on the invocations admitted by `Ok`. It is stated from Core runs
only. `Ok` is the admission predicate of `coreStratXP` (a parameter there too); the domain of
its theorems is `InvOkXP tags`. Internal Wasm calls are Core steps, so the internal call graph is
invisible; but the log is exact and the whole store is visible at every host callout, in every
host answer and at the end, so `PubEquivXP` is the equivalence of the exact-log public
observations, not a contextual equivalence and not contextual full abstraction.

**The public strategy.** `coreTripleXP P host Ok` is the observation triple underlying
`coreStratXP P host Ok`; `pubStratXP P host Ok s a` is the canonical play object of its public
restriction `pubTriple` (of `Silmaril.Wasm.Abstract.PubModule`) to the export `(s, a)`. An
exception `t` with final store `s₂` is the public answer `(.inr t, s₂)`.

**Not stated here.** No comparison with the native semantics (`NatObsXP`, `natStratXP`): that
waits for the backward square of `Silmaril.Wasm.Abstract.HostSquareXP` (the converse directions
for divergence and productive runs, not yet proved).

Theorems in `Silmaril.Wasm.Abstract.PubModuleXP.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The public interaction equivalence with exceptions** of two exports `(s, a)` and
`(s', a')` against `host` at the profile `P`, on the invocations admitted by `Ok`: for every
argument list `vs` and host log `cs`, the same values with final store, the same uncaught
exceptions with final store, the same traps, the same blocked and host-divergent callouts and the
same host-free divergence at exactly `cs`, and the same productive runs. -/
def PubEquivXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) (s : Store H) (a : Nat) (s' : Store H) (a' : Nat) :
    Prop :=
  ∀ vs : List Val,
    (∀ (cs : List (Call (wasmHostSig H))) (ws : List Val) (s₂ : Store H),
      (Ok s (a, vs) ∧ EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩) ↔
        (Ok s' (a', vs) ∧ EvRun P host (invoke s' a' vs) cs ⟨s₂, {}, vals ws⟩)) ∧
    (∀ (cs : List (Call (wasmHostSig H))) (t : Nat) (s₂ : Store H),
      (Ok s (a, vs) ∧ EvRun P host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩) ↔
        (Ok s' (a', vs) ∧ EvRun P host (invoke s' a' vs) cs ⟨s₂, {}, throwing t⟩)) ∧
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

/-- The Core observation triple with exceptions underlying `coreStratXP P host Ok`. -/
abbrev coreTripleXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  obsTriple Ok fun s q => CoreObsLXP P host s q.1 q.2

/-- **The public module strategy with exceptions** of the export `(s, a)`, from Core runs. -/
def pubStratXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) (s : Store H) (a : Nat) :
    DStrategy (wasmHostSig H) (pubSig H) :=
  StratObs.toDStrat (pubTriple (coreTripleXP P host Ok) s a)

end Silmaril.Wasm.Abstract
