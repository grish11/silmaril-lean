module

public import Silmaril.Games.Abstract.SessionHost.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DPair.Defs
public import Silmaril.Games.DivComp.Defs
import Silmaril.Proofs.Games.Abstract.SessionHost.Pair
import Silmaril.Proofs.Games.Abstract.SessionHost.Plays
import Silmaril.Proofs.Games.Abstract.SessionHost.Div
import Silmaril.Proofs.Games.Abstract.SessionHost.Inf

/-!
# A session with host imports beside component imports: theorems

The host imports `E` of a session `threadS t s₀ : DStrategy (E ⊕ₛ F) (sig1 A B)` are served by
the host beside copycat `(hostDOn F R).pair (DStrategy.id F)`, which answers them per `R` and
forwards the component imports `F` unchanged; the composite hides the host interaction.

**Finite plays** (`pair_comp_threadS_toStrategy`, no hypothesis): the composite has the finite
plays of the linked session `threadS (hostLinkS R t) s₀`. The interaction is tracked through the
host beside copycat, an automaton answering one host call or forwarding one component call at a
time (it is the pairing). A play of the composite is the visible part of a play of the session of
`t` whose host answers `R` allows, up to the forwarded component move in flight; such a play runs
the linked automaton on its visible part, the stores unchanged. Conversely a run of the linked
automaton is built back from its end: the call prefix of `t` witnessing the last visible call
fixes the hidden host calls before it.

**Divergence** (`pair_comp_threadS_div`, no hypothesis): the composite diverges exactly where the
linked session does. A divergence of `t` after allowed host answers, and the host diverging at a
call prefix, are local divergences. Hidden chatter of the composite (`DStrategy.comp`) is an
infinite interaction with a constant visible part: the session of `t` then streams inside one
round (it cannot complete infinitely many rounds, each of which is visible), with boundedly, hence
finitely, many component calls, every host answer allowed; that is the linked chatter divergence.

**Infinite plays.** Every infinite play of the composite is one of the linked session
(`pair_comp_threadS_inf_subset`, no hypothesis): the session of `t` streams inside a round with
infinitely many component calls (their limit is a linked productive stream), or completes
infinitely many rounds whose every finite prefix is completed. Conversely
(`threadS_inf_subset_pair_comp`) under `StoreDet (hostLinkS R t)`: a linked infinite play
completing infinitely many rounds needs one interaction extending round by round, but the linked
session only requires every finite prefix of its rounds to be completed
(`StratThread.not_coherent`), each possibly through different hidden host answers. Store
determinism makes the linked rounds coherent, and a coherent sequence is lifted round by round.

**Linking is composition with hiding** (`pair_comp_threadS`): under `StoreDet (hostLinkS R t)`,

  `((hostDOn F R).pair (DStrategy.id F)).comp (threadS t s₀) = threadS (hostLinkS R t) s₀`.

No `NoPlainTrap t` is needed: a plain trap of `t` after allowed host answers is a plain trap of
the linked triple, and ends both sessions alike. Neither is `StoreDet t` enough for the converse:
a hidden host answer may choose among stores that the visible log does not determine.

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionHost`.
-/

public section

namespace Silmaril.Games.Abstract.SessionHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratSession

universe u

variable {E F : Sig.{u}} {S A B : Type u}

/-- **The finite plays of a session with host imports**: the composite of the host beside copycat
and the session of `t` has the finite plays of the linked session. -/
theorem pair_comp_threadS_toStrategy (R : HostRel E)
    (t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1})) (s₀ : S) :
    (((hostDOn F R).pair (DStrategy.id F)).comp (threadS t s₀)).toStrategy =
      (threadS (hostLinkS R t) s₀).toStrategy := by
  rw [Silmaril.Proofs.Games.Abstract.SessionHost.pair_eq]
  exact Strategy.ext fun _ => Silmaril.Proofs.Games.Abstract.SessionHost.mem_comp_iff

/-- **The divergences of a session with host imports**: the composite of the host beside copycat
and the session of `t` diverges exactly where the linked session does. -/
theorem pair_comp_threadS_div (R : HostRel E) (t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1}))
    (s₀ : S) :
    (((hostDOn F R).pair (DStrategy.id F)).comp (threadS t s₀)).div =
      (threadS (hostLinkS R t) s₀).div := by
  rw [Silmaril.Proofs.Games.Abstract.SessionHost.pair_eq]
  exact Silmaril.Proofs.Games.Abstract.SessionHost.comp_div

/-- **Infinite plays of the composite are linked infinite plays.** -/
theorem pair_comp_threadS_inf_subset (R : HostRel E)
    (t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1})) (s₀ : S) :
    (((hostDOn F R).pair (DStrategy.id F)).comp (threadS t s₀)).inf ⊆
      (threadS (hostLinkS R t) s₀).inf := by
  rw [Silmaril.Proofs.Games.Abstract.SessionHost.pair_eq]
  exact fun _ => Silmaril.Proofs.Games.Abstract.SessionHost.inf_fwd

/-- **Linked infinite plays are infinite plays of the composite**, for a store-deterministic
linked triple. -/
theorem threadS_inf_subset_pair_comp {R : HostRel E}
    {t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1})} (hL : StratThread.StoreDet (hostLinkS R t))
    (s₀ : S) :
    (threadS (hostLinkS R t) s₀).inf ⊆
      (((hostDOn F R).pair (DStrategy.id F)).comp (threadS t s₀)).inf := by
  rw [Silmaril.Proofs.Games.Abstract.SessionHost.pair_eq]
  exact fun _ => Silmaril.Proofs.Games.Abstract.SessionHost.inf_bwd hL

/-- **Linking host imports is composition with hiding**: the host beside copycat composed with
the session of `t` is the session of the linked triple. -/
theorem pair_comp_threadS {R : HostRel E} {t : ObsTriple (E ⊕ₛ F) S A (B ⊕ PUnit.{u + 1})}
    (hL : StratThread.StoreDet (hostLinkS R t)) (s₀ : S) :
    ((hostDOn F R).pair (DStrategy.id F)).comp (threadS t s₀) = threadS (hostLinkS R t) s₀ :=
  DStrategy.ext (pair_comp_threadS_toStrategy R t s₀) (pair_comp_threadS_div R t s₀)
    ((pair_comp_threadS_inf_subset R t s₀).antisymm (threadS_inf_subset_pair_comp hL s₀))

end Silmaril.Games.Abstract.SessionHost
