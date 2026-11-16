module

public import Silmaril.Games.Abstract.SessionLinkCoh.Defs
public import Silmaril.Games.Abstract.SessionLinkAssoc.Thms
public import Silmaril.Games.Abstract.SessionCat.Defs
import Silmaril.Proofs.Games.Abstract.SessionLinkCoh.Coh

/-!
# Coherence of linking sessions (theorems)

Together with `SessionLinkAssoc`, sessions under `SessionLink.linkS` form a bicategory-like
structure up to store isomorphism. No hypotheses are needed.

**Functoriality of transport.** `mapStore (Equiv.refl S) t = t` (`mapStore_refl`) and
`mapStore (e.trans e') t = mapStore e' (mapStore e t)` (`mapStore_trans`). Transport commutes with
saturation (`sat_mapStore`) and with dropping plain traps (`dropTrap_mapStore`): neither looks at
stores beyond the argument store.

**Naturality.** `linkS` commutes with transport of the server store (`linkS_mapStore_left`) and of
the client store (`linkS_mapStore_right`), along `Equiv.prodCongr`: a served round of
`mapStore e t` from `s` is a round of `t` from `e.symm s`, and coherent services transport store by
store; a round of `mapStore e' u` at `s'` is a round of `u` at `e'.symm s'`, with the same calls.

**Invariance.** `linkS` reads only the returning and divergent rounds, the call prefixes and the
productive streams of its server, and only the finished behaviours, call prefixes and productive
streams of its client: `linkS (dropTrap (sat t)) u = linkS t u` (`linkS_dropTrap_sat_left`) and
`linkS t (sat u) = linkS t u` (`linkS_sat_right`).

**Pentagon.** The two reassociations of `linkS (linkS (linkS t u) v) w` into
`linkS t (linkS u (linkS v w))`, by `linkS_assoc` twice (`linkS_assoc4_two`, along `assoc4Two`)
or by `linkS_assoc` three times and naturality (`linkS_assoc4_three`, along `assoc4Three`), are
the same transport: `assoc4Two = assoc4Three` (`assoc4Two_eq_assoc4Three`), the pentagon of
`Equiv.prodAssoc`.

**Triangle.** Unlike the unit laws themselves, the triangle holds for every server and client:
`linkS (linkS t idS) u = mapStore (unitRight S S') (linkS t u)` (`linkS_linkS_idS`), since `linkS`
does not see the saturation and the plain traps that `linkS_idS` introduces, and
`linkS t (linkS idS u) = mapStore _ (linkS t u)` (`linkS_idS_linkS`) since it does not see the
saturation of the client. The route through associativity (`linkS_linkS_idS_assoc`, along
`unitAssocLeft`) agrees: `unitAssocLeft = unitRight` (`unitAssocLeft_eq_unitRight`).

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionLinkCoh`.
-/

public section

namespace Silmaril.Games.Abstract.SessionLinkCoh

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.SessionLink
  Silmaril.Games.Abstract.SessionLinkAssoc Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}}

/-! ## Transport -/

section Transport

variable {S S' S'' A B : Type u}

/-- Transport along the identity is the identity. -/
theorem mapStore_refl (t : ObsTriple E S A B) : mapStore (Equiv.refl S) t = t :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.mapStore_refl t

/-- Transport along a composite is the composite of transports. -/
theorem mapStore_trans (e : S ≃ S') (e' : S' ≃ S'') (t : ObsTriple E S A B) :
    mapStore (e.trans e') t = mapStore e' (mapStore e t) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.mapStore_trans e e' t

/-- Transport commutes with saturation. -/
theorem sat_mapStore (e : S ≃ S') (t : ObsTriple E S A B) :
    sat (mapStore e t) = mapStore e (sat t) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.sat_mapStore e t

/-- Transport commutes with dropping plain traps. -/
theorem dropTrap_mapStore (e : S ≃ S') (t : ObsTriple E S A B) :
    dropTrap (mapStore e t) = mapStore e (dropTrap t) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.dropTrap_mapStore e t

end Transport

/-! ## Naturality and invariance of `linkS` -/

section Natural

variable {S S' T T' A B A' B' : Type u}

/-- **Naturality in the server store.** -/
theorem linkS_mapStore_left (e : S ≃ T) (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    linkS (mapStore e t) u = mapStore (Equiv.prodCongr e (Equiv.refl S')) (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_mapStore_left e t u

/-- **Naturality in the client store.** -/
theorem linkS_mapStore_right (e : S' ≃ T') (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    linkS t (mapStore e u) = mapStore (Equiv.prodCongr (Equiv.refl S) e) (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_mapStore_right e t u

/-- Linking does not see the saturation of the client. -/
theorem linkS_sat_right (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    linkS t (sat u) = linkS t u :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_sat_right t u

/-- Linking does not see the saturation of the server, nor its plain traps once saturated. -/
theorem linkS_dropTrap_sat_left (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
    (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})) :
    linkS (dropTrap (sat t)) u = linkS t u :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_dropTrap_sat_left t u

end Natural

/-! ## Pentagon -/

/-- **The pentagon** of `Equiv.prodAssoc`: both reassociations are the same equivalence. -/
theorem assoc4Two_eq_assoc4Three (S₁ S₂ S₃ S₄ : Type u) :
    assoc4Two S₁ S₂ S₃ S₄ = assoc4Three S₁ S₂ S₃ S₄ :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.assoc4Two_eq_assoc4Three S₁ S₂ S₃ S₄

section Pentagon

variable {S₁ S₂ S₃ S₄ A B A' B' A'' B'' A''' B''' : Type u}
  (t : ObsTriple E S₁ A (B ⊕ PUnit.{u + 1}))
  (u : ObsTriple (sig1 A B) S₂ A' (B' ⊕ PUnit.{u + 1}))
  (v : ObsTriple (sig1 A' B') S₃ A'' (B'' ⊕ PUnit.{u + 1}))
  (w : ObsTriple (sig1 A'' B'') S₄ A''' (B''' ⊕ PUnit.{u + 1}))

/-- Reassociating a fourfold link by `linkS_assoc` twice. -/
theorem linkS_assoc4_two :
    linkS (linkS (linkS t u) v) w =
      mapStore (assoc4Two S₁ S₂ S₃ S₄) (linkS t (linkS u (linkS v w))) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_assoc4_two t u v w

/-- Reassociating a fourfold link by `linkS_assoc` three times, with naturality. -/
theorem linkS_assoc4_three :
    linkS (linkS (linkS t u) v) w =
      mapStore (assoc4Three S₁ S₂ S₃ S₄) (linkS t (linkS u (linkS v w))) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_assoc4_three t u v w

end Pentagon

/-! ## Triangle -/

/-- **The triangle** of `Equiv.prodAssoc` with the unitors. -/
theorem unitAssocLeft_eq_unitRight (S S' : Type u) : unitAssocLeft S S' = unitRight S S' :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.unitAssocLeft_eq_unitRight S S'

section Triangle

variable {S S' A B A' B' : Type u} (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
  (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1}))

/-- Removing the identity on the right of the server, for any server and client. -/
theorem linkS_linkS_idS :
    linkS (linkS t idS) u = mapStore (unitRight S S') (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_linkS_idS t u

/-- Removing the identity on the left of the client, for any server and client. -/
theorem linkS_idS_linkS :
    linkS t (linkS idS u) = mapStore (Equiv.prodCongr (Equiv.refl S) (Equiv.punitProd S').symm)
      (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_idS_linkS t u

/-- Removing the identity through associativity and the left unit. -/
theorem linkS_linkS_idS_assoc :
    linkS (linkS t idS) u = mapStore (unitAssocLeft S S') (linkS t u) :=
  Silmaril.Proofs.Games.Abstract.SessionLinkCoh.linkS_linkS_idS_assoc t u

end Triangle

end Silmaril.Games.Abstract.SessionLinkCoh
