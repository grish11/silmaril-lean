module

public import Silmaril.Games.Abstract.StratHost.Defs
import Silmaril.Proofs.Games.Abstract.StratHost.Basic

/-!
# Restricting an open play object by a relational host: theorems

* `consistent_iff_lift`: a log is allowed by `R` exactly when it is the image of a log of the
  legal interface `legalSig E R.legal`;
* `restrict_hostRestrict`: **the host restriction is the legal restriction plus a pending
  filter**. On the legal interface the behaviours and the productive streams of
  `hostRestrict R t` are those of `restrict R.legal t`, and its pending calls are those of
  `restrict R.legal t` at which `R` stalls.

Proofs are in `Silmaril.Proofs.Games.Abstract.StratHost.Basic`.
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

end Silmaril.Games.Abstract.StratHost
