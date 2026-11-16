module

public import Silmaril.Games.Abstract.SessionLink.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DivComp.Defs
import Silmaril.Proofs.Games.Abstract.SessionLink.Plays

/-!
# Linking sessions: theorems

The server session `threadS t s₀ : DStrategy E (sig1 A B)` serves the imports of the client
session `threadS u s₀' : DStrategy (sig1 A B) (sig1 A' B')`; their composite
`(threadS t s₀).comp (threadS u s₀')` hides the interaction on `sig1 A B`.

**The linked triple is saturated** (`saturated_linkS`): every call forced by a linked behaviour
or stream is a pending call of the linked triple, a call prefix of the server inside a served call.

**Finite plays** (`comp_threadS_toStrategy`): for a server without plain traps
(`StratSession.NoPlainTrap`), the finite plays of the composite are those of the session of the
linked triple, `threadS (linkS t u) (s₀, s₀')`. The interaction is tracked by relating the states
of the three session automata: while the client runs a round, the server is idle at the store
reached by the rounds that served the client's calls so far, and the linked automaton runs the
same round at the stores of the round's start; while the client waits on a call, the server runs
the session round serving it. Conversely each linked run is realized by an interaction, built
round by round from the witnesses of the linked behaviours and pending calls.

`NoPlainTrap t` is needed: a plain trap of the server answers `.inr ()` and kills the server
session, so a later call of the client is never answered, which the store `S × S'` cannot record.

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionLink`.
-/

public section

namespace Silmaril.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratThread
  Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

/-- **The linked triple is saturated**: its call prefixes are its pending calls. -/
theorem saturated_linkS : Saturated (linkS t u) :=
  saturated_iff.2 <| funext fun _ => funext fun _ => Set.ext fun _ =>
    ⟨Silmaril.Proofs.Games.Abstract.SessionLink.satP_linkS, .inl⟩

/-- **The finite plays of linked sessions**: for a server without plain traps, the composite of
the server session and the client session has the finite plays of the linked session. -/
theorem comp_threadS_toStrategy (hnt : NoPlainTrap t) (s₀ : S) (s₀' : S') :
    ((threadS t s₀).comp (threadS u s₀')).toStrategy =
      (threadS (linkS t u) (s₀, s₀')).toStrategy :=
  Strategy.ext fun _ => Silmaril.Proofs.Games.Abstract.SessionLink.mem_comp_iff hnt

end Silmaril.Games.Abstract.SessionLink
