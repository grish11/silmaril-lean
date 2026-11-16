module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetOps
public import Silmaril.Logic.SetTheory.Universes.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSem

universe u
open ZFSet
open Silmaril.Logic.SetTheory

noncomputable section

/-- A graph is contained in a product as soon as its values are in the codomain. -/
theorem lam_subset_prod {A D : ZFSet.{u}} {g : ZFSet.{u} → ZFSet.{u}}
    (hg : ∀ a ∈ A, g a ∈ D) : lam A g ⊆ ZFSet.prod A D := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := mem_lam.1 hz
  exact ZFSet.pair_mem_prod.2 ⟨ha, hg a ha⟩

/-- A dependent product is a set of graphs bounded by one function space. -/
theorem pi_subset_powerset_prod {A D : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hB : ∀ a ∈ A, B a ⊆ D) : pi A B ⊆ powerset (ZFSet.prod A D) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := mem_pi.1 hf
  exact mem_powerset.2 (lam_subset_prod fun a ha => hB a ha (hg a ha))

/-- A dependent sum is contained in the product with any common fibre bound. -/
theorem sigma_subset_prod {A D : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hB : ∀ a ∈ A, B a ⊆ D) : sigma A B ⊆ ZFSet.prod A D := by
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sigma.1 hp
  exact ZFSet.pair_mem_prod.2 ⟨ha, hB a ha hb⟩

/-- Grothendieck universes are closed under dependent products. -/
theorem pi_mem {U A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hU : IsGrothendieckUniverse U) (hA : A ∈ U) (hB : ∀ a ∈ A, B a ∈ U) :
    pi A B ∈ U := by
  let D : ZFSet.{u} := ⋃ a : A, B a.1
  have hD : D ∈ U := hU.iUnion_mem A hA (fun a => B a.1) (fun a => hB a.1 a.2)
  apply hU.subset_mem (hU.powerset_mem _ (hU.prod_mem hA hD))
  exact pi_subset_powerset_prod fun a ha => ZFSet.subset_iUnion (fun a : A => B a.1) ⟨a, ha⟩

/-- Grothendieck universes are closed under dependent sums. -/
theorem sigma_mem {U A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hU : IsGrothendieckUniverse U) (hA : A ∈ U) (hB : ∀ a ∈ A, B a ∈ U) :
    sigma A B ∈ U := by
  let D : ZFSet.{u} := ⋃ a : A, B a.1
  have hD : D ∈ U := hU.iUnion_mem A hA (fun a => B a.1) (fun a => hB a.1 a.2)
  apply hU.subset_mem (hU.prod_mem hA hD)
  exact sigma_subset_prod fun a ha => ZFSet.subset_iUnion (fun a : A => B a.1) ⟨a, ha⟩

/-- Identity types belong to every Grothendieck universe. -/
theorem truth_mem {U : ZFSet.{u}} (hU : IsGrothendieckUniverse U) (p : Prop) :
    truth p ∈ U := by
  classical
  by_cases hp : p
  · simpa [truth, hp, tt] using hU.singleton_mem hU.empty_mem
  · simpa [truth, hp] using hU.empty_mem

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetSem
