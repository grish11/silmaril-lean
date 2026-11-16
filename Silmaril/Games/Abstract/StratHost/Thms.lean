module

public import Silmaril.Games.Abstract.StratHost.Defs
public import Silmaril.Games.DivComp.Defs
import Silmaril.Proofs.Games.Abstract.StratHost.Basic
import Silmaril.Proofs.Games.Abstract.StratHost.Link

/-!
# Restricting an open play object by a relational host: theorems

* `consistent_iff_lift`: a log is allowed by `R` exactly when it is the image of a log of the
  legal interface `legalSig E R.legal`;
* `restrict_hostRestrict`: **the host restriction is the legal restriction plus a pending
  filter**. On the legal interface the behaviours and the productive streams of
  `hostRestrict R t` are those of `restrict R.legal t`, and its pending calls are those of
  `restrict R.legal t` at which `R` stalls.

**Linking is interaction plus hiding** (`comp_hostD_toDStrat`):
`(hostD R).comp (toDStrat t) = toDStrat (linkT R t)`, all three components (finite plays,
divergence, infinite plays). Composing with the host hides every host interaction:

* a completed round of the composite is a behaviour of `t` whose log `R` allows, log erased;
* the composite diverges after a question when `t` diverges after an allowed log, when `R` may
  diverge at a call prefix of `t` after an allowed log (`hostD` diverges), or when `t` has a
  productive stream with every answer allowed: infinitely many hidden host interactions, the
  chatter clause of `DStrategy.comp`. No other divergence arises: an infinite interaction with a
  constant visible part cannot complete infinitely many rounds, so the upper limit is a stream;
* a call prefix at which `R` has no outcome is quiescent in the composite: no move and no
  divergence. The composite does not distinguish it from an unanswered question;
* the infinite plays of the composite are exactly those completing infinitely many rounds.

Proofs are in `Silmaril.Proofs.Games.Abstract.StratHost.Basic` and `.Link`.
-/

public section

namespace Silmaril.Games.Abstract.StratHost

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratLegal

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- The logs `R` allows are the logs of the legal interface, legality forgotten. -/
theorem consistent_iff_lift (R : HostRel E) (cs : List (Call E)) :
    R.Consistent cs ↔ ∃ c : List (Call (legalSig E R.legal)), c.map liftCall = cs :=
  Silmaril.Proofs.Games.Abstract.StratHost.consistent_iff R cs

/-- **The host restriction is the legal restriction plus a pending filter**: the legal
restriction keeps every pending call after an allowed prefix, the host restriction only those at
which `R` stalls. -/
theorem restrict_hostRestrict (R : HostRel E) (t : ObsTriple E S A B) :
    restrict R.legal (hostRestrict R t) =
      ((restrict R.legal t).1, fun s a => {x | x ∈ (restrict R.legal t).2.1 s a ∧ R.Stalls x.2},
        (restrict R.legal t).2.2) :=
  Silmaril.Proofs.Games.Abstract.StratHost.restrict_hostRestrict R t

/-- **Linking is interaction plus hiding**: the play object of `t` composed with the host `R`,
host interaction hidden, is the play object of the closed triple `linkT R t`. -/
theorem comp_hostD_toDStrat (R : HostRel E) (t : ObsTriple E S A B) :
    (hostD R).comp (StratObs.toDStrat t) = StratObs.toDStrat (linkT R t) :=
  Silmaril.Proofs.Games.Abstract.StratHost.comp_hostD_toDStrat

end Silmaril.Games.Abstract.StratHost
