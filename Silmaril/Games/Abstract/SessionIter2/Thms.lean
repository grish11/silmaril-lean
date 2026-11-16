module

public import Silmaril.Games.Abstract.SessionIter2.Defs
public import Silmaril.Games.Abstract.SessionIter.Thms
import Silmaril.Proofs.Games.Abstract.SessionIter2.Det
import Silmaril.Proofs.Games.Abstract.SessionIter2.Frame

/-!
# Session iteration: determinism of sequencing and store strength (theorems)

**Determinism** (proof in `Silmaril.Proofs.Games.Abstract.SessionIter2.Det`). `det_seqS`:
session sequencing preserves determinism given answers (`AFun.Det`), with no further
hypothesis. Sequencing hides no calls, so the obstruction for linking
(`SessionLinkCex.not_det_linkS_may`: a hidden call to a diverging server makes a return and a
divergence with the same log) does not arise: two behaviours of `seqS t u` agree on their
`t`-parts, and when those end alike, in the same value and store, on their `u`-parts.

**Store strength** (proofs in `…SessionIter2.Frame`). `frameS_iterT`, `frameS_iterS`: store
strength commutes with iteration, on the nose. A framed body leaves the second store component
untouched, so its finite behaviours, continuing chains and infinite continuing chains from
`(s, s')` are those of the body from `s` with `s'` attached.
-/

public section

namespace Silmaril.Games.Abstract.SessionIter2

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratOps
  Silmaril.Games.Abstract.StratSession Silmaril.Games.Abstract.SessionCat
  Silmaril.Games.Abstract.SessionIter

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-! ## Determinism -/

/-- **Session sequencing preserves determinism given answers.** -/
theorem det_seqS {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {u : ObsTriple E S B (C ⊕ PUnit.{u + 1})} (ht : AFun.Det t.1) (hu : AFun.Det u.1) :
    AFun.Det (seqS t u).1 :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.det_seqS ht hu

/-! ## Store strength -/

/-- **Store strength commutes with iteration of triples.** -/
theorem frameS_iterT {S' : Type u} (t : ObsTriple E S A (B ⊕ A)) :
    frameS S' (iterT t) = iterT (frameS S' t) :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.frameS_iterT t

/-- **Store strength commutes with session iteration.** -/
theorem frameS_iterS {S' : Type u} (t : ObsTriple E S A ((B ⊕ A) ⊕ PUnit.{u + 1})) :
    frameS S' (iterS t) = iterS (frameS S' t) :=
  Silmaril.Proofs.Games.Abstract.SessionIter2.frameS_iterS t

end Silmaril.Games.Abstract.SessionIter2
