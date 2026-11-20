module

public import Silmaril.Semantics.Accept.Parse.Cursor.Defs
public import Silmaril.Semantics.Accept.Parse.Thms
import Silmaril.Proofs.Semantics.Accept.Parse.Cursor

/-!
# Parsing sessions: the cursor under every overrun policy

The cursor laws of `Silmaril.Accept.Parse` (`run_cursor`, `parseRel_slice`) count every `used`
(`consumed`) and so require the session-abort overrun policy. With the effective count
`effConsumed`, which counts only answered finishes, they hold for **every** overrun policy, in
particular the call-local trap `callTrap` (the default) and `ignore`:

* `run_cursor_eff`: along a run ending live, the buffer is the fed input after the effectively
  consumed prefix, and that count never exceeds the input (every policy: an undefined-behaviour
  overrun never comes back to a live state);
* `parseRel_slice_eff`: every accepted pair of a chunked module relates exactly the `used` slice
  after the effective cursor (overrun and bad-handle policies without undefined behaviour);
* `effConsumed_eq_consumed`: under `sessionTrap`, along a live run the effective count is the
  plain count, so `run_cursor` and `parseRel_slice` are the special case; `effConsumed_le`: the
  effective count never exceeds the plain one.
-/

@[expose] public section

namespace Silmaril.Accept.Parse

open Silmaril.Accept.Handle

universe u v w

variable {V : Type u} {H : Type v} {X : Type w}

theorem effConsumed_le (n : Nat) (t : List (PEv V H)) : effConsumed n t ≤ consumed t :=
  Silmaril.Proofs.Semantics.Accept.Parse.effConsumed_le n t

variable [DecidableEq H] {pol : PPolicy H}

/-- **The cursor invariant under every overrun policy.** -/
theorem run_cursor_eff {ρ : Env H X} {s s' : PState V} {t : List (PEv V H)}
    {A : Set (List V × X)} (hr : (parser pol ρ).Run s t s' A) (hc : ChunkOnly t)
    (hl : s'.phase = .live) :
    s'.buf = (s.buf ++ fed t).drop (effConsumed s.buf.length t) ∧
      effConsumed s.buf.length t ≤ (s.buf ++ fed t).length :=
  Silmaril.Proofs.Semantics.Accept.Parse.run_cursor_eff hr hc hl

/-- **Under the session-abort policy the effective count is the plain count.** -/
theorem effConsumed_eq_consumed {ρ : Env H X} (ho : pol.onOverrun = .sessionTrap)
    {s s' : PState V} {t : List (PEv V H)} {A : Set (List V × X)}
    (hr : (parser pol ρ).Run s t s' A) (hc : ChunkOnly t) (hl : s'.phase = .live) :
    effConsumed s.buf.length t = consumed t :=
  Silmaril.Proofs.Semantics.Accept.Parse.effConsumed_eq_consumed ho hr hc hl

/-- **Chunked parsing relates the `used` slice after the effective cursor**, for every overrun
policy without undefined behaviour (in particular the call-local trap). -/
theorem parseRel_slice_eff (ho : pol.onOverrun ≠ .ub) (hb : pol.onBadHandle ≠ .ub)
    {Envs : Set (Env H X)} {T : Set (List (PEv V H))} (hT : ∀ t ∈ T, ChunkOnly t)
    {p : List V × X} (hp : p ∈ parseRel pol Envs T) :
    ∃ t ∈ T, ∃ u n h v, t = u ++ PEv.finish n h :: v ∧
      p.1 = ((fed u).drop (effConsumed 0 u)).take n ∧ effConsumed 0 u + n ≤ (fed u).length ∧
      h ≠ pol.sentinel ∧ ∃ ρ ∈ Envs, ρ h = some p.2 :=
  Silmaril.Proofs.Semantics.Accept.Parse.rel_slice_eff ho hb hT hp

end Silmaril.Accept.Parse
