module

public import Silmaril.Games.Abstract.StratSession.Defs
public import Silmaril.Games.Abstract.StratHost.Defs

/-!
# A session with host imports beside component imports

A component `t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit)` (a store-retaining triple, `StratSession`)
calls two kinds of imports: **host imports** `E`, served by a relational host `R : HostRel E`
(`HostRun`), and **component imports** `F`, served by other components and left visible. Its
session is `threadS t s₀ : DStrategy (E ⊕ₛ F) (sig1 A B)`.

**The host beside copycat.** `hostDOn F R : DStrategy F E` is the host `StratHost.hostD R` on
the lower interface `F`, where it makes no calls: its plays are the legal plays with no move on
`F` whose answers `R` allows; it diverges after a call at which `R` may diverge; at a call with no
outcome it has no move and does not diverge; every limit of its plays is an infinite play. For
`F = Sig.empty` it is `hostD R` (`SessionHost.hostDOn_empty`). The strategy answering the host
imports and forwarding the component imports is the pairing
`(hostDOn F R).pair (DStrategy.id F) : DStrategy F (E ⊕ₛ F)` (`DPair`), and the session with its
host imports linked is the composite `((hostDOn F R).pair (DStrategy.id F)).comp (threadS t s₀)`
(`DivComp`).

**The linked triple** `hostLinkS R t : ObsTriple F S A (B ⊕ PUnit)` (for any result type).
Its logs are the `F`-calls of logs of `t` (`fCalls`) whose host answers `R` allows
(`(sumL R F).Consistent`, where `sumL R F` is `R` on the left summand and allows every answer on
`F`). At the store `s` and the question `a`:

* **behaviours**: every behaviour `(c, e)` of `t` with an allowed log, any end (values,
  continuing traps `.ret (.inr ()) s'`, plain traps and divergence kept), log `fCalls c`;
* **host divergence**: a call prefix `(c, .inl m)` of `t` (`StratObs.satP`) with an allowed log at
  which `R` may diverge: `div`, log `fCalls c`;
* **hidden chatter**: a productive stream of `t` with every answer allowed and only host calls
  after its first `n` calls (infinitely many hidden host interactions): `div`, log the
  `F`-calls of the first `n` calls;
* **pending calls**: the call prefixes `(c, .inr m)` of `t` with an allowed log, as the visible
  call `m` after `fCalls c`;
* **productive streams**: the `F`-calls `ω'` of a productive stream of `t` with every answer
  allowed and infinitely many `F`-calls.

A call prefix `(c, .inl m)` at which `R` has no outcome gives nothing: the session waits forever
at the visible prefix `fCalls c`, with no further move and no divergence. Since the stores are
those of `t`, a continuing trap continues the linked session, and a plain trap ends it.

Theorems in `Silmaril.Games.Abstract.SessionHost.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract.StratObs

universe u

variable {E F : Sig.{u}} {S A B : Type u}

/-! ## The host on a lower interface -/

/-- A move the host on `F` may play: no move on `F`, any question, an allowed answer. -/
def HostMove (R : HostRel E) : Move F E → Prop
  | .inl _ => False
  | .inr (.ask _) => True
  | .inr (.ans m n) => R m (.answer n)

/-- Without moves on the lower interface a play never waits for a lower answer. -/
theorem path_not_wait {R : HostRel E} {x y : Pos F E} {s : List (Move F E)} (h : Path x s y)
    (hs : ∀ o ∈ s, HostMove R o) (hx : ∀ q m, x ≠ .wait q m) : ∀ q m, y ≠ .wait q m := by
  induction h with
  | nil => exact hx
  | cons st _ ih =>
    refine ih (fun o ho => hs o (.tail _ ho)) ?_
    have h0 := hs _ (.head _)
    cases st <;> simp_all [HostMove]

/-- The finite plays of the host on `F`: legal plays of host moves. -/
def hostOnS (F : Sig.{u}) (R : HostRel E) : Strategy F E where
  plays := {s | Legal s ∧ ∀ o ∈ s, HostMove R o}
  nil_mem := ⟨Legal.nil, fun _ h => nomatch h⟩
  legal h := h.1
  of_prefix := fun ⟨hl, ho⟩ hst => ⟨hl.of_prefix hst, fun o h => ho o (hst.subset h)⟩
  receptive := fun ⟨_, ho⟩ hx hxy hO => ⟨⟨_, hx.append (.single hxy)⟩, fun o h => by
    rcases List.mem_append.1 h with h | h
    · exact ho o h
    · cases List.mem_singleton.1 h
      cases hxy with
      | ask => trivial
      | reply q m n => exact absurd rfl (path_not_wait hx ho (fun _ _ h => nomatch h) q m)
      | call => exact hO.elim
      | ret => exact hO.elim⟩

/-- **The host `R` on the lower interface `F`**: it makes no call on `F`, answers each call `m` of
`E` with an answer `R` allows, diverges at the calls where `R` may diverge, and is quiescent at the
calls `R` has no outcome for. Every limit of its plays is an infinite play. -/
def hostDOn (F : Sig.{u}) (R : HostRel E) : DStrategy F E where
  toStrategy := hostOnS F R
  div := {s | s ∈ hostOnS F R ∧ ∃ m, Path .idle s (.run m) ∧ R m .diverge}
  inf := {I | IsInfPlay I ∧ I ⊆ (hostOnS F R).plays}
  div_mem h := h.1
  div_run := fun ⟨_, m, h, _⟩ => ⟨m, h⟩
  inf_isInf h := h.1
  inf_sub h := h.2

/-! ## The linked triple -/

/-- `R` on the host imports; every answer of a component import is allowed. -/
def sumL (R : HostRel E) (F : Sig.{u}) : HostRel (E ⊕ₛ F)
  | .inl m, o => R m o
  | .inr _, _ => True

/-- The component call of a call, if it is one. -/
def fCall : Call (E ⊕ₛ F) → List (Call F)
  | ⟨.inl _, _⟩ => []
  | ⟨.inr m, n⟩ => [⟨m, n⟩]

/-- **The component calls of a log**: the host calls are hidden. -/
def fCalls : List (Call (E ⊕ₛ F)) → List (Call F)
  | [] => []
  | x :: c => fCall x ++ fCalls c

/-- **The linked triple**: `t` with its host imports served by `R` and hidden, its component
imports visible. See the module documentation. -/
def hostLinkS (R : HostRel E) (t : ObsTriple (E ⊕ₛ F) S A B) : ObsTriple F S A B :=
  (fun s a => {x |
      -- a behaviour of `t` with an allowed log
      (∃ c, (c, x.2) ∈ t.1 s a ∧ (sumL R F).Consistent c ∧ x.1 = fCalls c) ∨
      (x.2 = .div ∧
        -- the host diverges at a call prefix
        ((∃ c m, (c, .inl m) ∈ satP t s a ∧ (sumL R F).Consistent c ∧ R m .diverge ∧
            x.1 = fCalls c) ∨
        -- hidden chatter: only host calls after the first `n`
        ∃ ω ∈ hostObsInf (sumL R F) t.2.2 s a, ∃ n, (∀ k, n ≤ k → fCall (ω k) = []) ∧
          x.1 = fCalls (streamTake ω n)))},
    fun s a => {x | ∃ c, (c, .inr x.2) ∈ satP t s a ∧ (sumL R F).Consistent c ∧ x.1 = fCalls c},
    fun s a => {ω' | ∃ ω ∈ hostObsInf (sumL R F) t.2.2 s a,
      (∀ n, ∃ k, n ≤ (fCalls (streamTake ω k)).length) ∧
      ∀ k, streamTake ω' (fCalls (streamTake ω k)).length = fCalls (streamTake ω k)})

end Silmaril.Games.Abstract.SessionHost
