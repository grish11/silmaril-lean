module

public import Silmaril.Games.Abstract.SessionHost.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Games.DPair.Defs
public import Silmaril.Games.DivComp.Defs
import Silmaril.Proofs.Games.Abstract.SessionHost.Pair
import Silmaril.Proofs.Games.Abstract.SessionHost.Plays

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

end Silmaril.Games.Abstract.SessionHost
