module

public import Silmaril.Logic.SetTheory.Universes.Defs
import Silmaril.Proofs.Logic.SetTheory.Universes

@[expose] public section

/-!
# Universe closure and lifting theorems

The lower carrier embeds faithfully into the next carrier. Its image is a
Grothendieck universe, so concrete finite towers can be constructed using
successively larger Lean universes.
-/

namespace Silmaril.Logic.SetTheory

universe u v

open ZFSet

theorem mem_liftSet {x : ZFSet.{u}} {y : ZFSet.{max u v}} :
    y ∈ liftSet.{u, v} x ↔ ∃ z ∈ x, liftSet z = y :=
  Silmaril.Proofs.Logic.SetTheory.mem_liftSet

theorem liftSet_mem_liftSet {x y : ZFSet.{u}} (h : x ∈ y) :
    liftSet.{u, v} x ∈ liftSet y :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_mem_liftSet h

theorem liftSet_injective : Function.Injective liftSet.{u, v} :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_injective

@[simp] theorem liftSet_inj {x y : ZFSet.{u}} :
    liftSet.{u, v} x = liftSet y ↔ x = y :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_inj

@[simp] theorem liftSet_mem_liftSet_iff {x y : ZFSet.{u}} :
    liftSet.{u, v} x ∈ liftSet y ↔ x ∈ y :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_mem_liftSet_iff

theorem liftSet_empty : liftSet.{u, v} ∅ = ∅ :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_empty

theorem liftSet_insert (x y : ZFSet.{u}) :
    liftSet.{u, v} (insert x y) = insert (liftSet x) (liftSet y) :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_insert x y

theorem liftSet_pair (x y : ZFSet.{u}) :
    liftSet.{u, v} {x, y} = {liftSet x, liftSet y} :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_pair x y

/-- Concrete carrier lifting preserves singleton sets. -/
theorem liftSet_singleton (x : ZFSet.{u}) : liftSet.{u, v} {x} = {liftSet.{u, v} x} :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_singleton x

/-- Concrete carrier lifting preserves Kuratowski ordered pairs. -/
theorem liftSet_orderedPair (x y : ZFSet.{u}) :
    liftSet.{u, v} (ZFSet.pair x y) = ZFSet.pair (liftSet.{u, v} x) (liftSet.{u, v} y) :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_orderedPair x y

theorem liftSet_powerset (x : ZFSet.{u}) :
    liftSet.{u, v} (powerset x) = powerset (liftSet x) :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_powerset x

theorem liftSet_sUnion (x : ZFSet.{u}) :
    liftSet.{u, v} (⋃₀ x) = ⋃₀ liftSet x :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_sUnion x

/-- Concrete carrier lifting preserves each finite von Neumann ordinal. -/
theorem liftSet_numeral (n : ℕ) :
    liftSet.{u, v} (Silmaril.Logic.SetTheory.numeral n) = Silmaril.Logic.SetTheory.numeral n :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_numeral n

theorem liftSet_omega : liftSet.{u, v} omega = omega :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_omega

theorem small_liftSet (x : ZFSet.{u}) : Small.{u} (liftSet.{u, v} x) :=
  Silmaril.Proofs.Logic.SetTheory.small_liftSet x

theorem mem_universeSet {x : ZFSet.{u + 1}} :
    x ∈ universeSet ↔ ∃ a, liftSet.{u, u + 1} a = x :=
  Silmaril.Proofs.Logic.SetTheory.mem_universeSet

theorem liftSet_mem_universeSet (x : ZFSet.{u}) :
    liftSet.{u, u + 1} x ∈ universeSet :=
  Silmaril.Proofs.Logic.SetTheory.liftSet_mem_universeSet x

theorem universeSet_eq_mk_embed :
    universeSet.{u} = ZFSet.mk PSet.embed.{u, u + 1} :=
  Silmaril.Proofs.Logic.SetTheory.universeSet_eq_mk_embed

theorem universeSet_isTransitive : universeSet.{u}.IsTransitive :=
  Silmaril.Proofs.Logic.SetTheory.universeSet_isTransitive

theorem mem_universeSet_iff_small {z : ZFSet.{u + 1}} (hz : z ⊆ universeSet) :
    z ∈ universeSet ↔ Small.{u} z :=
  Silmaril.Proofs.Logic.SetTheory.mem_universeSet_iff_small hz

theorem small_of_mem_universeSet {x : ZFSet.{u + 1}} (hx : x ∈ universeSet) :
    Small.{u} x :=
  Silmaril.Proofs.Logic.SetTheory.small_of_mem_universeSet hx

theorem omega_mem_universeSet : (omega : ZFSet.{u + 1}) ∈ universeSet.{u} :=
  Silmaril.Proofs.Logic.SetTheory.omega_mem_universeSet

/-- The next Lean set carrier contains the universe of all lower-level sets. -/
theorem isGrothendieckUniverse_universeSet : IsGrothendieckUniverse universeSet.{u} :=
  Silmaril.Proofs.Logic.SetTheory.isGrothendieckUniverse_universeSet

namespace IsGrothendieckUniverse

variable {U x y : ZFSet.{u}}

/-- The empty set belongs to every Grothendieck universe. -/
theorem empty_mem (h : IsGrothendieckUniverse U) : (∅ : ZFSet.{u}) ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.empty_mem h

/-- A subset of a member belongs to the universe. -/
theorem subset_mem (h : IsGrothendieckUniverse U) (hy : y ∈ U) (hxy : x ⊆ y) : x ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.subset_mem h hy hxy

theorem singleton_mem (h : IsGrothendieckUniverse U) (hx : x ∈ U) : ({x} : ZFSet.{u}) ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.singleton_mem h hx

theorem sUnion_mem (h : IsGrothendieckUniverse U) (hx : x ∈ U) : (⋃₀ x) ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.sUnion_mem h hx

theorem union_mem (h : IsGrothendieckUniverse U) (hx : x ∈ U) (hy : y ∈ U) : x ∪ y ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.union_mem h hx hy

theorem insert_mem (h : IsGrothendieckUniverse U) (hx : x ∈ U) (hy : y ∈ U) : insert x y ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.insert_mem h hx hy

/-- Kuratowski pairs of members belong to the universe. -/
theorem opair_mem (h : IsGrothendieckUniverse U) (hx : x ∈ U) (hy : y ∈ U) :
    ZFSet.pair x y ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.opair_mem h hx hy

/-- An image of a member by a universe-valued function belongs to the universe. -/
theorem range_mem (h : IsGrothendieckUniverse U) (hx : x ∈ U)
    (f : x → ZFSet.{u}) (hf : ∀ i, f i ∈ U) : ZFSet.range f ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.range_mem h hx f hf

theorem prod_mem (h : IsGrothendieckUniverse U) (hx : x ∈ U) (hy : y ∈ U) :
    ZFSet.prod x y ∈ U :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.prod_mem h hx hy

/-- A lifted universe retains the Grothendieck closure properties. -/
theorem liftSet (h : IsGrothendieckUniverse U) :
    IsGrothendieckUniverse (Silmaril.Logic.SetTheory.liftSet.{u, v} U) :=
  Silmaril.Proofs.Logic.SetTheory.IsGrothendieckUniverse.liftSet h

end IsGrothendieckUniverse

end Silmaril.Logic.SetTheory
