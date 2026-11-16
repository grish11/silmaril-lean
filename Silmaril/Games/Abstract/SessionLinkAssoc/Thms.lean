module

public import Silmaril.Games.Abstract.SessionLinkAssoc.Defs
public import Silmaril.Games.Abstract.SessionCat.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
import Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.Unit

/-!
# Linking sessions: literal associativity and units (theorems)

The category laws of `SessionLink.linkS` as equalities of triples, after transporting the store
along an equivalence (`mapStore`). No determinism hypotheses are needed; unlike the session-level
laws of `SessionCat`, these compare the observations themselves.

**Units** (no hypotheses):

* `linkS_idS`: the identity client served by `t` is `t` with the store `S × PUnit`, saturated and
  with its plain traps dropped: `linkS t idS = mapStore (prodPUnit S).symm (dropTrap (sat t))`.
  A linked round is one round of `t` (a return, a continuing trap or a divergence); its pending
  calls are the call prefixes of `t`; `linkS` ignores the plain traps of its server.
* `idS_linkS`: the client `u` served by the identity server is `u` with the store `PUnit × S`,
  saturated: `linkS idS u = mapStore (punitProd S).symm (sat u)`. The identity server answers
  each call at once with that call, so a linked round is a round of `u` and its log is the list of
  calls of `u`; the identity server never diverges and every one of its rounds makes a call, so
  there is no hidden chatter.

**Before saturation.** The literal unit laws hold exactly on the expected domain:
`linkS t idS = mapStore _ (sat t) ↔ NoPlainTrap t` (`linkS_idS_eq_sat_iff`),
`linkS t idS = mapStore _ t ↔ NoPlainTrap t ∧ Saturated t` (`linkS_idS_eq_iff`) and
`linkS idS u = mapStore _ u ↔ Saturated u` (`idS_linkS_eq_iff`). Counterexamples: the plain
trap `trapT` (`linkS_trapT_idS_ne`) and the unsaturated `callDivT` (`idS_linkS_callDivT_ne`),
whose call forces a pending call that it does not list.

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionLinkAssoc`.
-/

public section

namespace Silmaril.Games.Abstract.SessionLinkAssoc

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionCat Silmaril.Games.Abstract.StratSession

universe u

variable {E : Sig.{u}}

/-! ## Transport -/

/-- Transport back along the inverse equivalence. -/
theorem mapStore_symm_mapStore {S S' A B : Type u} (e : S ≃ S') (t : ObsTriple E S A B) :
    mapStore e.symm (mapStore e t) = t :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.mapStore_symm_mapStore e t

/-- Transport is injective. -/
theorem mapStore_injective {S S' A B : Type u} (e : S ≃ S') :
    Function.Injective (mapStore (E := E) (A := A) (B := B) e) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.mapStore_injective e

/-! ## Units -/

section Unit

variable {S A B A' B' : Type u}

/-- **Right unit**: the identity client served by `t` is `t`, saturated, without plain traps. -/
theorem linkS_idS (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) :
    linkS t idS = mapStore (Equiv.prodPUnit S).symm (dropTrap (sat t)) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.linkS_idS t

/-- **Left unit**: the client `u` served by the identity server is `u`, saturated. -/
theorem idS_linkS (u : ObsTriple (sig1 A B) S A' (B' ⊕ PUnit.{u + 1})) :
    linkS idS u = mapStore (Equiv.punitProd S).symm (sat u) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.idS_linkS u

/-- The right unit law up to saturation holds exactly for servers without plain traps. -/
theorem linkS_idS_eq_sat_iff {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} :
    linkS t idS = mapStore (Equiv.prodPUnit S).symm (sat t) ↔ NoPlainTrap t :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.linkS_idS_eq_sat_iff

/-- The literal right unit law holds exactly for saturated servers without plain traps. -/
theorem linkS_idS_eq_iff {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} :
    linkS t idS = mapStore (Equiv.prodPUnit S).symm t ↔ NoPlainTrap t ∧ Saturated t :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.linkS_idS_eq_iff

/-- The literal left unit law holds exactly for saturated clients. -/
theorem idS_linkS_eq_iff {u : ObsTriple (sig1 A B) S A' (B' ⊕ PUnit.{u + 1})} :
    linkS idS u = mapStore (Equiv.punitProd S).symm u ↔ Saturated u :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.idS_linkS_eq_iff

/-- A plain server trap breaks the right unit law, even up to saturation. -/
theorem linkS_trapT_idS_ne :
    linkS (trapT (E := E)) idS ≠ mapStore (Equiv.prodPUnit _).symm (sat trapT) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.linkS_trapT_idS_ne

/-- An unsaturated client breaks the literal left unit law. -/
theorem idS_linkS_callDivT_ne :
    linkS idS callDivT.{u} ≠ mapStore (Equiv.punitProd _).symm callDivT.{u} :=
  Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.idS_linkS_callDivT_ne

end Unit

end Silmaril.Games.Abstract.SessionLinkAssoc
