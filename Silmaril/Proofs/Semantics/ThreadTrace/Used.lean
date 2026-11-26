module

public import Silmaril.Semantics.ThreadTrace.Defs
import Silmaril.Proofs.Semantics.ThreadTrace.Monads

public section

namespace Silmaril.Proofs.Semantics.ThreadTrace

open Silmaril.ThreadTrace

universe u

variable {T W A B : Type u} [Monoid W]

theorem memFresh (t : T) (used final : Set T) (a : T) (w : W) :
    ((a, final), w) ∈ (fresh (W := W)).run t used ↔
      t ∈ used ∧ a ∉ used ∧ final = insert a used ∧ w = 1 := Iff.rfl

theorem freshNonempty (t : T) (used : Set T) :
    ((fresh (W := W)).run t used).Nonempty ↔ t ∈ used ∧ ∃ a, a ∉ used := by
  constructor
  · rintro ⟨⟨⟨a, final⟩, w⟩, h⟩
    obtain ⟨ht, ha, _, _⟩ := (memFresh t used final a w).mp h
    exact ⟨ht, a, ha⟩
  · rintro ⟨ht, a, ha⟩
    exact ⟨((a, insert a used), 1), (memFresh t used _ a 1).mpr ⟨ht, ha, rfl, rfl⟩⟩

theorem pureRespectsUsed {resultSupport : A → Set T} {outputSupport : W → Set T}
    {a : A} (ha : ∀ (t : T) used, t ∈ used → resultSupport a ⊆ used)
    (hOne : outputSupport 1 = ∅) :
    (pure a : Alloc T W A).RespectsUsed resultSupport outputSupport := by
  intro t used b final w ht h
  change ((b, final), w) ∈ ({((a, used), 1)} : Set (Branch T W A)) at h
  simp only [Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨Set.Subset.rfl, ha t _ ht, hOne.symm ▸ Set.empty_subset _⟩

theorem bindRespectsUsed {supportA : A → Set T} {supportB : B → Set T}
    {outputSupport : W → Set T}
    (hMul : ∀ v w, outputSupport (v * w) ⊆ outputSupport v ∪ outputSupport w)
    {x : Alloc T W A} {k : A → Alloc T W B}
    (hx : x.RespectsUsed supportA outputSupport)
    (hk : ∀ a t used, t ∈ used → supportA a ⊆ used →
      ∀ b final w, ((b, final), w) ∈ (k a).run t used →
        used ⊆ final ∧ supportB b ⊆ final ∧ outputSupport w ⊆ final) :
    (x >>= k).RespectsUsed supportB outputSupport := by
  intro t used b final w ht hw
  obtain ⟨a, middle, v, w', hv, hw', rfl⟩ := (memAllocBind x k t used final b w).mp hw
  obtain ⟨hg, ha, hv⟩ := hx ht hv
  obtain ⟨hg', hb, hw'⟩ := hk a t middle (hg ht) ha b final w' hw'
  exact ⟨hg.trans hg', hb, (hMul v w').trans (Set.union_subset (hv.trans hg') hw')⟩

theorem freshRespectsUsed {outputSupport : W → Set T} (hOne : outputSupport 1 = ∅) :
    (fresh (W := W)).RespectsUsed (fun a => {a}) outputSupport := by
  intro t used a final w _ hw
  obtain ⟨_, _, rfl, rfl⟩ := (memFresh t used final a w).mp hw
  exact ⟨Set.subset_insert _ _, Set.singleton_subset_iff.mpr (Set.mem_insert _ _),
    hOne.symm ▸ Set.empty_subset _⟩

end Silmaril.Proofs.Semantics.ThreadTrace
