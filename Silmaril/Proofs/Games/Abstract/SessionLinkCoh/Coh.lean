module

public import Silmaril.Proofs.Games.Abstract.SessionLinkCoh.Natural
public import Silmaril.Games.Abstract.SessionLinkCoh.Defs
public import Silmaril.Games.Abstract.SessionCat.Defs

/-!
# Coherence of linking sessions: pentagon and triangle (proofs)

The pentagon and triangle identities of the store equivalences hold pointwise by `rfl`; the two
reassociations of a fourfold link and the two unit removals of a threefold link are obtained from
`linkS_assoc`, the unit laws and naturality.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkCoh

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionLinkAssoc
  Silmaril.Games.Abstract.SessionLinkCoh Silmaril.Games.Abstract.SessionCat

universe u

variable {E : Sig.{u}}

theorem assoc4Two_eq_assoc4Three (S₁ S₂ S₃ S₄ : Type u) :
    assoc4Two S₁ S₂ S₃ S₄ = assoc4Three S₁ S₂ S₃ S₄ :=
  Equiv.ext fun ⟨_, _, _, _⟩ => rfl

theorem unitAssocLeft_eq_unitRight (S S' : Type u) : unitAssocLeft S S' = unitRight S S' :=
  Equiv.ext fun ⟨_, _⟩ => rfl

section Pentagon

variable {S₁ S₂ S₃ S₄ A B A' B' A'' B'' A''' B''' : Type u}
  (t : ObsTriple E S₁ A (B ⊕ PUnit.{u + 1}))
  (u : ObsTriple (sig1 A B) S₂ A' (B' ⊕ PUnit.{u + 1}))
  (v : ObsTriple (sig1 A' B') S₃ A'' (B'' ⊕ PUnit.{u + 1}))
  (w : ObsTriple (sig1 A'' B'') S₄ A''' (B''' ⊕ PUnit.{u + 1}))

theorem linkS_assoc4_two :
    linkS (linkS (linkS t u) v) w =
      mapStore (assoc4Two S₁ S₂ S₃ S₄) (linkS t (linkS u (linkS v w))) := by
  rw [linkS_assoc, linkS_assoc, assoc4Two, mapStore_trans]

theorem linkS_assoc4_three :
    linkS (linkS (linkS t u) v) w =
      mapStore (assoc4Three S₁ S₂ S₃ S₄) (linkS t (linkS u (linkS v w))) := by
  rw [linkS_assoc t u v, linkS_mapStore_left, linkS_assoc, linkS_assoc u v w,
    linkS_mapStore_right, assoc4Three, mapStore_trans, mapStore_trans]

end Pentagon

section Triangle

variable {S S' A B A' B' : Type u} (t : ObsTriple E S A (B ⊕ PUnit.{u + 1}))
  (u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1}))

theorem linkS_linkS_idS :
    linkS (linkS t idS) u = mapStore (unitRight S S') (linkS t u) := by
  rw [linkS_idS, linkS_mapStore_left, linkS_dropTrap_sat_left, unitRight]

theorem linkS_idS_linkS :
    linkS t (linkS idS u) = mapStore (Equiv.prodCongr (Equiv.refl S) (Equiv.punitProd S').symm)
      (linkS t u) := by
  rw [idS_linkS, linkS_mapStore_right, linkS_sat_right]

theorem linkS_linkS_idS_assoc :
    linkS (linkS t idS) u = mapStore (unitAssocLeft S S') (linkS t u) := by
  rw [linkS_assoc, linkS_idS_linkS, unitAssocLeft, mapStore_trans]

end Triangle

end Silmaril.Proofs.Games.Abstract.SessionLinkCoh
