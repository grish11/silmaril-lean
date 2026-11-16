module

public import Silmaril.Games.Abstract.SessionLink.Defs

/-!
# Linking servers with plain traps

`SessionLink.linkS t u` serves a call of the client `u` only by a *returning* round of the server
`t`, the server store threaded in `S × S'`; the store has no state for a dead server, so a plain
trap `End.trap` of the server is ignored, and `SessionLink.comp_threadS` assumes
`NoPlainTrap t` (`SessionLinkCex.comp_ne_linkS_plainTrap` shows it is needed). In the session
`threadS t s₀`, a plain trap answers the current call with `.inr ()` and ends the server session:
the next question is never answered.

**The dead server.** `deadS t : ObsTriple E (Option S) A (B ⊕ PUnit)` records that end in the
store: `some s` is the live server at `s`, `none` the dead server. At `some s`, `deadS t` has

* the returns of `t` (values and continuing traps `.ret (.inr ()) s₁`), at `some s₁`;
* each plain trap of `t` with the log `c` as the continuing trap `.ret (.inr ()) none` to the
  dead server, **unless** `t` also has a continuing trap with the log `c`;
* the divergences, pending calls and productive streams of `t`.

At `none` it has nothing: no behaviour, no pending call, no stream, so a question to the dead
server is never answered, and a client calling it waits forever, quiescent.

**Why a shadowed plain trap is dropped.** If `t` has, with the same log, both a plain trap and a
continuing trap to `s₁`, the session cannot tell them apart: after the answer `.inr ()`, the
dead server only accepts the next question, which the server at `s₁` accepts too. Keeping both in
`deadS t` would make it store-nondeterministic (the same log and answer reaching `none` and
`some s₁`) even for a store-deterministic `t`; dropping the plain one keeps
`StratThread.StoreDet t → StoreDet (deadS t)` and `AFun.Det t.1 → AFun.Det (deadS t).1`, and does
not change the session (`SessionLinkDead.Thms.threadS_deadS`).

**Linking with a dead server.** `linkSD t u : ObsTriple E (Option S × S') A' (B' ⊕ PUnit)` is
`linkS (deadS t) u`: after a plain server trap the server store is `none`, and a later round of
the client that calls the server has no linked behaviour, pending call or stream past that call.
When `t` has no plain trap, `deadS t` is `t` at the stores `some s`, and `linkSD t u` is
`linkS t u` along the embedding `(s, s') ↦ (some s, s')`.

Theorems in `Silmaril.Games.Abstract.SessionLinkDead.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionLinkDead

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u}

/-- The finished behaviours of the live server at `s`: returns of `t`, plain traps of `t` not
shadowed by a continuing trap with the same log (to the dead server `none`), and divergences. -/
def deadBeh (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) (s : S) (a : A) :
    Set (CallBeh E (Option S) (B ⊕ PUnit.{u + 1})) :=
  {x | (∃ y s₁, (x.1, End.ret y s₁) ∈ t.1 s a ∧ x.2 = End.ret y (some s₁)) ∨
    ((x.1, End.trap) ∈ t.1 s a ∧ (∀ s₁, (x.1, End.ret (.inr PUnit.unit) s₁) ∉ t.1 s a) ∧
      x.2 = End.ret (.inr PUnit.unit) none) ∨
    ((x.1, End.div) ∈ t.1 s a ∧ x.2 = End.div)}

/-- **The server with a dead state**: a plain trap goes to the dead server `none`, which never
answers. -/
def deadS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) :
    ObsTriple E (Option S) A (B ⊕ PUnit.{u + 1}) :=
  (fun σ a => σ.elim ∅ fun s => deadBeh t s a,
    fun σ a => σ.elim ∅ fun s => t.2.1 s a,
    fun σ a => σ.elim ∅ fun s => t.2.2 s a)

/-- **Linking with a server that may die**: the client `u` served by `deadS t`. -/
def linkSD (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    ObsTriple E (Option S × S') A' (B' ⊕ PUnit.{u + 1}) :=
  SessionLink.linkS (deadS t) u

/-- The end of a round of `linkS t u` along the embedding `(s, s') ↦ (some s, s')`. -/
def someEnd : End (S × S') B → End (Option S × S') B
  | .ret b σ => .ret b (some σ.1, σ.2)
  | .trap => .trap
  | .div => .div

end Silmaril.Games.Abstract.SessionLinkDead
