module

public import Silmaril.Games.Abstract.StratLegal.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
import Silmaril.Proofs.Games.Abstract.StratLegal.Basic

/-!
# Legal call/answer interfaces for the canonical play object: theorems

* `restrict_admissible`: restricting an admissible triple to legal answers keeps it admissible;
* `mem_satP_restrict`: on an admissible triple, the call prefixes of the restriction are the
  pending calls of `t` with legal answers;
* `mem_toDStratL` (**the legal game embeds**): for an admissible triple, a play of the legal
  interface is a play of `toDStratL L t` exactly when, legality forgotten, it is a play of
  `toDStrat t`. So the plays of `toDStratL L t` are the plays of `toDStrat t` whose Opponent
  import answers are all legal, read on the legal interface;
* `toDStratL_eq_iff`, `toDStratL_injective`: the legal play object identifies exactly the
  triples with the same saturated restriction; on admissible triples, exactly the same
  restriction.

Only the plays with legal answers are compared: two triples that differ only on illegally
answered logs have the same legal play object.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.StratLegal

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B : Type u} {L : (m : E.Op) → E.Ar m → Prop}
  {t t' : ObsTriple E S A B}

/-- On an admissible triple, the call prefixes of the restriction are the legally answered
pending calls. -/
theorem mem_satP_restrict (ht : Admissible t) {s : S} {a : A}
    {x : List (Call (legalSig E L)) × E.Op} :
    x ∈ satP (restrict L t) s a ↔ (x.1.map liftCall, x.2) ∈ t.2.1 s a :=
  Silmaril.Proofs.Games.Abstract.StratLegal.mem_satP_restrict ht

/-- **Restriction keeps admissibility.** -/
theorem restrict_admissible (ht : Admissible t) : Admissible (restrict L t) :=
  Silmaril.Proofs.Games.Abstract.StratLegal.restrict_admissible ht

/-- **The legal game embeds**: on an admissible triple, the plays of the legal play object are
the plays of `toDStrat t` with legal import answers. -/
theorem mem_toDStratL (ht : Admissible t) {s : List (Move (legalSig E L) (funSig S A B))} :
    s ∈ (toDStratL L t).toStrategy ↔ s.map liftMove ∈ (toDStrat t).toStrategy :=
  Silmaril.Proofs.Games.Abstract.StratLegal.mem_toDStratL ht

/-- The legal play object identifies exactly the triples with the same saturated restriction. -/
theorem toDStratL_eq_iff : toDStratL L t = toDStratL L t' ↔ sat (restrict L t) = sat (restrict L t') :=
  toDStrat_eq_iff

/-- **On admissible triples, the legal play object is injective modulo restriction.** -/
theorem toDStratL_injective (ht : Admissible t) (ht' : Admissible t') :
    toDStratL L t = toDStratL L t' ↔ restrict L t = restrict L t' :=
  ⟨toDStrat_injective (restrict_admissible ht) (restrict_admissible ht'),
    fun h => congrArg StratObs.toDStrat h⟩

end Silmaril.Games.Abstract.StratLegal
