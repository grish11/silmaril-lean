module

public import Silmaril.Semantics.ThreadTrace.Defs

public section

namespace Silmaril.Proofs.Semantics.ThreadTrace

open Silmaril.ThreadTrace

universe u

variable {T W V A B : Type u}

theorem nondetExt {x y : Nondet T W A} (h : ∀ t, x.run t = y.run t) : x = y :=
  funext h

theorem allocExt {x y : Alloc T W A} (h : ∀ t used, x.run t used = y.run t used) : x = y :=
  funext fun t => funext (h t)

theorem singletonInjective : Function.Injective (singleton (T := T) (W := W) (A := A)) := by
  intro x y h
  funext t
  have ht := congrArg (fun x : Nondet T W A => x.run t) h
  exact Set.singleton_injective ht

theorem ignoreUsedInjective : Function.Injective (ignoreUsed (T := T) (W := W) (A := A)) := by
  intro x y h
  exact funext fun t => congrArg (fun x : ReadOnly T W A => x t ∅) h

theorem readOnlyInjective : Function.Injective (readOnly (T := T) (W := W) (A := A)) := by
  intro x y h
  funext t used
  have ht := congrArg (fun x : Alloc T W A => x.run t used) h
  exact Set.image_injective.mpr (fun ⟨_, _⟩ ⟨_, _⟩ h =>
    congrArg (fun b : Branch T W A => (b.1.1, b.2)) h) ht

theorem memReadOnly (x : ReadOnly T W A) (t : T) (used final : Set T) (a : A) (w : W) :
    ((a, final), w) ∈ (readOnly x).run t used ↔ final = used ∧ (a, w) ∈ x.run t used := by
  change (∃ z ∈ x.run t used, ((z.1, used), z.2) = ((a, final), w)) ↔ _
  constructor
  · rintro ⟨⟨b, v⟩, hb, he⟩
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, h⟩
    exact ⟨(a, w), h, rfl⟩

theorem readOnlyRange (x : Alloc T W A) : x ∈ Set.range readOnly ↔
    ∀ t used a final w, ((a, final), w) ∈ x.run t used → final = used := by
  constructor
  · rintro ⟨y, rfl⟩ t used a final w h
    exact ((memReadOnly y t used final a w).mp h).1
  · intro h
    refine ⟨fun t used => WriterT.mk (show Set (A × W) from {b | ((b.1, used), b.2) ∈ x.run t used}), ?_⟩
    apply allocExt
    intro t used
    ext ⟨⟨a, final⟩, w⟩
    rw [memReadOnly]
    exact ⟨fun ⟨he, hb⟩ => he.symm ▸ hb, fun hb => ⟨h t used a final w hb, h t used a final w hb ▸ hb⟩⟩

variable [Monoid W]

theorem memNondetBind (x : Nondet T W A) (k : A → Nondet T W B) (t : T) (b : B) (w : W) :
    (b, w) ∈ (x >>= k).run t ↔
      ∃ a w₁ w₂, (a, w₁) ∈ x.run t ∧ (b, w₂) ∈ (k a).run t ∧ w₁ * w₂ = w := by
  change (b, w) ∈ ⋃ y ∈ x.run t, (fun z : B × W => (z.1, y.2 * z.2)) '' (k y.1).run t ↔ _
  simp only [Set.mem_iUnion, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, w₁, h₁, _, w₂, h₂, rfl, rfl⟩
    exact ⟨a, w₁, w₂, h₁, h₂, rfl⟩
  · rintro ⟨a, w₁, w₂, h₁, h₂, rfl⟩
    exact ⟨a, w₁, h₁, b, w₂, h₂, rfl, rfl⟩

theorem memAllocBind (x : Alloc T W A) (k : A → Alloc T W B) (t : T)
    (used final : Set T) (b : B) (w : W) :
    ((b, final), w) ∈ (x >>= k).run t used ↔
      ∃ a middle w₁ w₂, ((a, middle), w₁) ∈ x.run t used ∧
        ((b, final), w₂) ∈ (k a).run t middle ∧ w₁ * w₂ = w := by
  change ((b, final), w) ∈ ⋃ y ∈ x.run t used,
    (fun z : Branch T W B => (z.1, y.2 * z.2)) '' (k y.1.1).run t y.1.2 ↔ _
  simp only [Set.mem_iUnion, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, middle, w₁, h₁, _, _, w₂, h₂, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨a, middle, w₁, w₂, h₁, h₂, rfl⟩
  · rintro ⟨a, middle, w₁, w₂, h₁, h₂, rfl⟩
    exact ⟨a, middle, w₁, h₁, b, final, w₂, h₂, ⟨rfl, rfl⟩, rfl⟩

theorem singletonBind (x : Det T W A) (k : A → Det T W B) :
    singleton (x >>= k) = singleton x >>= fun a => singleton (k a) := by
  apply nondetExt
  intro t
  ext ⟨b, v⟩
  rw [memNondetBind]
  change (b, v) ∈ {((k (x.run t).1).run t |>.1, (x.run t).2 * ((k (x.run t).1).run t).2)} ↔
    ∃ a w₁ w₂, (a, w₁) ∈ {x.run t} ∧ (b, w₂) ∈ {(k a).run t} ∧ w₁ * w₂ = v
  rcases x.run t with ⟨a, w⟩
  rcases hk : (k a).run t with ⟨c, z⟩
  simp [hk, eq_comm]

theorem readOnlyBind (x : ReadOnly T W A) (k : A → ReadOnly T W B) :
    readOnly (x >>= k) = readOnly x >>= fun a => readOnly (k a) := by
  apply allocExt
  intro t used
  ext ⟨⟨b, final⟩, w⟩
  simp only [memReadOnly, memAllocBind]
  change (final = used ∧ (b, w) ∈ (x t >>= fun a => k a t).run used) ↔ _
  rw [memNondetBind]
  constructor
  · rintro ⟨rfl, a, w₁, w₂, ha, hb, rfl⟩
    exact ⟨a, _, w₁, w₂, ⟨rfl, ha⟩, ⟨rfl, hb⟩, rfl⟩
  · rintro ⟨a, middle, w₁, w₂, ⟨hm, ha⟩, ⟨hf, hb⟩, rfl⟩
    subst middle final
    exact ⟨rfl, a, w₁, w₂, ha, hb, rfl⟩

variable [Monoid V] (q : W →* V)

theorem detMapBind (x : Det T W A) (k : A → Det T W B) :
    Det.mapOutput q (x >>= k) = Det.mapOutput q x >>= fun a => Det.mapOutput q (k a) := by
  funext t
  change ((k (x.run t).1).run t |>.1, q ((x.run t).2 * ((k (x.run t).1).run t).2)) =
    ((k (x.run t).1).run t |>.1, q (x.run t).2 * q ((k (x.run t).1).run t).2)
  rw [map_mul]

theorem memNondetMapOutput (x : Nondet T W A) (t : T) (a : A) (v : V) :
    (a, v) ∈ (Nondet.mapOutput q x).run t ↔ ∃ w, (a, w) ∈ x.run t ∧ q w = v := by
  change (∃ z ∈ x.run t, (z.1, q z.2) = (a, v)) ↔ _
  constructor
  · rintro ⟨⟨b, w⟩, hw, h⟩
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(a, w), hw, rfl⟩

theorem memMapOutput (x : Alloc T W A) (t : T) (used final : Set T) (a : A) (v : V) :
    ((a, final), v) ∈ (Alloc.mapOutput q x).run t used ↔
      ∃ w, ((a, final), w) ∈ x.run t used ∧ q w = v := by
  change (∃ z ∈ x.run t used, (z.1, q z.2) = ((a, final), v)) ↔ _
  constructor
  · rintro ⟨⟨⟨b, last⟩, w⟩, hw, h⟩
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨((a, final), w), hw, rfl⟩

theorem nondetMapBind (x : Nondet T W A) (k : A → Nondet T W B) :
    Nondet.mapOutput q (x >>= k) = Nondet.mapOutput q x >>= fun a => Nondet.mapOutput q (k a) := by
  apply nondetExt
  intro t
  ext ⟨b, w⟩
  simp only [memNondetMapOutput, memNondetBind]
  constructor
  · rintro ⟨_, ⟨a, w₁, w₂, ha, hb, rfl⟩, rfl⟩
    exact ⟨a, q w₁, q w₂, ⟨w₁, ha, rfl⟩, ⟨w₂, hb, rfl⟩, (map_mul q _ _).symm⟩
  · rintro ⟨a, _, _, ⟨w₁, ha, rfl⟩, ⟨w₂, hb, rfl⟩, rfl⟩
    exact ⟨w₁ * w₂, ⟨a, w₁, w₂, ha, hb, rfl⟩, map_mul q _ _⟩

theorem allocMapBind (x : Alloc T W A) (k : A → Alloc T W B) :
    Alloc.mapOutput q (x >>= k) = Alloc.mapOutput q x >>= fun a => Alloc.mapOutput q (k a) := by
  apply allocExt
  intro t used
  ext ⟨⟨b, final⟩, w⟩
  simp only [memMapOutput, memAllocBind]
  constructor
  · rintro ⟨_, ⟨a, middle, w₁, w₂, ha, hb, rfl⟩, rfl⟩
    exact ⟨a, middle, q w₁, q w₂, ⟨w₁, ha, rfl⟩, ⟨w₂, hb, rfl⟩, (map_mul q _ _).symm⟩
  · rintro ⟨a, middle, _, _, ⟨w₁, ha, rfl⟩, ⟨w₂, hb, rfl⟩, rfl⟩
    exact ⟨w₁ * w₂, ⟨a, middle, w₁, w₂, ha, hb, rfl⟩, map_mul q _ _⟩

theorem allocMapPure (a : A) : Alloc.mapOutput q (pure a : Alloc T W A) = pure a := by
  apply allocExt
  intro t used
  change (fun z : Branch T W A => (z.1, q z.2)) '' {((a, used), 1)} = {((a, used), 1)}
  simp

theorem mapReadOnly (x : ReadOnly T W A) :
    Alloc.mapOutput q (readOnly x) = readOnly (ReadOnly.mapOutput q x) := by
  apply allocExt
  intro t used
  change (fun z : Branch T W A => (z.1, q z.2)) '' ((fun z : A × W => ((z.1, used), z.2)) '' x.run t used) =
    (fun z : A × V => ((z.1, used), z.2)) '' ((fun z : A × W => (z.1, q z.2)) '' x.run t used)
  simp only [Set.image_image]

end Silmaril.Proofs.Semantics.ThreadTrace
