module

public import Silmaril.Wasm.Abstract.HostSquare.Defs
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Defs

/-!
# The exact-log commuting square for the canonical closure: definitions

The canonical (exception-aware) analogue of `Silmaril.Wasm.Abstract.HostSquare`. The observations
are the same type `FullObs H`; on each side the log is exact.

* `NatObsXP host s a vs`: the canonical side, host-independent apart from the filter
  `coreHostRel host` on the answers: finished behaviours of `wasmEvFunXP` (values, an uncaught
  exception `ret (inr t) s₂` and a trap are all finished ends; `div` is none,
  `wasmEvFunXP_ne_div`), pending calls of `wasmEvPendXP` (with the host filters of `NatObs`),
  divergence after a log of `wasmEvFunDXP`, and productive runs of `wasmEvInfNXP`;
* `CoreObsLXP P host s a vs`: the Core side, as `CoreObsL` with the uncaught exception as a
  finished end: a labelled run (`EvRun`) with exactly the log to the thrown exception
  `throwing t` (`REF.EXN_ADDR t; THROW_REF`) at `s₂`, in the empty frame, the Core configuration
  of `HostClosingXP.wasmEvFunXP_throw_iff`. `End.div` is no finished Core end.

A trap is never caught on either side (`EvalLXPh` and Core pass a trap through every handler);
a productive run is never a `div` observation (`div` needs a finite log and no further host
call).

Theorems in `Silmaril.Wasm.Abstract.HostSquareXP.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The canonical observations**: the logged canonical semantics, its answers filtered by the
host. -/
def NatObsXP (host : HostSemantics H) (s : Store H) (a : Nat) (vs : List Val) :
    FullObs H → Prop
  | .done cs e => (cs, e) ∈ wasmEvFunXP s (a, vs) ∧ (coreHostRel host).Consistent cs
  | .blocked cs m => (cs, m) ∈ wasmEvPendXP s (a, vs) ∧ (coreHostRel host).Consistent cs ∧
      ∀ ans, ¬ coreHostRel host m ans
  | .hostDiv cs m => (cs, m) ∈ wasmEvPendXP s (a, vs) ∧ (coreHostRel host).Consistent cs ∧
      coreHostRel host m .diverge
  | .div cs => (cs, .div) ∈ wasmEvFunDXP s (a, vs) ∧ (coreHostRel host).Consistent cs
  | .prod ω => ω ∈ hostObsInf (coreHostRel host) wasmEvInfNXP s (a, vs)

/-- **The Core observations with exceptions**, at exactly their log: `CoreObsL` with the uncaught
exception `throwing t` as a finished end. -/
def CoreObsLXP (P : Numerics.Profile) (host : HostSemantics H) (s : Store H) (a : Nat)
    (vs : List Val) : FullObs H → Prop
  | .done cs (.ret (.inl ws) s₂) => EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩
  | .done cs (.ret (.inr t) s₂) => EvRun P host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩
  | .done cs .trap => ∃ s₂, EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩
  | .done _ .div => False
  | .blocked cs (hh, s', us) => ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat),
      EvRun P host (invoke s a vs) cs c ∧
      SingleThreaded.decompose? c.store c.code = some (E, a', hh, us) ∧ c.store = s' ∧
      ∀ o, ¬ host hh s' us o
  | .hostDiv cs (hh, s', us) => ∃ (c : Config H) (E : SingleThreaded.Ctx) (a' : Nat),
      EvRun P host (invoke s a vs) cs c ∧
      SingleThreaded.decompose? c.store c.code = some (E, a', hh, us) ∧ c.store = s' ∧
      host hh s' us .diverged
  | .div cs => ∃ c' : Config H, EvRun P host (invoke s a vs) cs c' ∧
      Diverges P (fun _ _ _ _ => False) c'
  | .prod ω => CoreInf P host (invoke s a vs) ω

end Silmaril.Wasm.Abstract
