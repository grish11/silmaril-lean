module

public import Silmaril.Semantics.ThreadTrace.Defs
import Silmaril.Proofs.Semantics.ThreadTrace.Monads
import Silmaril.Proofs.Semantics.ThreadTrace.Used

public section

namespace Silmaril.Proofs.Semantics.ThreadTrace

open Silmaril.ThreadTrace
open scoped Pointwise

universe u

variable {T W V A B : Type u} [Monoid W] [MulDistribMulAction (Equiv.Perm T) W]

theorem freshEquivariant : (fresh (T := T) (W := W)).Equivariant := by
  rintro p t used ⟨⟨a, final⟩, w⟩
  change ((p • a, p • final), p • w) ∈ (fresh (W := W)).run (p • t) (p • used) ↔ _
  have hw : p • w = 1 ↔ w = 1 := by
    have hOne : p • (1 : W) = 1 := smul_one p
    calc
      p • w = 1 ↔ p • w = p • (1 : W) := by rw [hOne]
      _ ↔ w = 1 := smul_left_cancel_iff p
  simp only [memFresh, Set.smul_mem_smul_set_iff, ← Set.smul_set_insert, smul_left_cancel_iff, hw]

variable [MulAction (Equiv.Perm T) A] [MulAction (Equiv.Perm T) B]

theorem singletonEquivariant (x : Det T W A) : (singleton x).Equivariant ↔ x.Equivariant := by
  constructor
  · intro hx p t
    exact (hx p t (x.run t)).mpr (Set.mem_singleton _)
  · intro hx p t b
    change (p • b ∈ ({x.run (p • t)} : Set (A × W))) ↔ b ∈ ({x.run t} : Set (A × W))
    rw [← hx p t, Set.mem_singleton_iff, Set.mem_singleton_iff, smul_left_cancel_iff]

theorem ignoreUsedEquivariant (x : Nondet T W A) : (ignoreUsed x).Equivariant ↔ x.Equivariant :=
  ⟨fun h p t b => h p t ∅ b, fun h p t _ b => h p t b⟩

theorem readOnlyEquivariant (x : ReadOnly T W A) : (readOnly x).Equivariant ↔ x.Equivariant := by
  have eval (p : Equiv.Perm T) (t : T) (used final : Set T) (a : A) (w : W) :
      (p • ((a, final), w) ∈ (readOnly x).run (p • t) (p • used) ↔
          ((a, final), w) ∈ (readOnly x).run t used) ↔
        ((final = used ∧ p • (a, w) ∈ x.run (p • t) (p • used)) ↔
          (final = used ∧ (a, w) ∈ x.run t used)) := by
    change ((((p • a, p • final), p • w) ∈ _) ↔ _) ↔ _
    simp only [memReadOnly, smul_left_cancel_iff, Prod.smul_mk]
  constructor
  · rintro hx p t used ⟨a, w⟩
    simpa only [true_and] using (eval p t used used a w).mp (hx p t used ((a, used), w))
  · rintro hx p t used ⟨⟨a, final⟩, w⟩
    exact (eval p t used final a w).mpr (and_congr_right fun _ => hx p t used (a, w))

theorem pureEquivariant (a : A) (ha : ∀ p : Equiv.Perm T, p • a = a) :
    (pure a : Alloc T W A).Equivariant := by
  intro p t used b
  change p • b ∈ ({((a, p • used), 1)} : Set (Branch T W A)) ↔
    b ∈ ({((a, used), 1)} : Set (Branch T W A))
  have h : p • ((a, used), (1 : W)) = ((a, p • used), 1) := by
    change ((p • a, p • used), p • (1 : W)) = _
    rw [ha, smul_one]
  rw [← h, Set.mem_singleton_iff, Set.mem_singleton_iff, smul_left_cancel_iff]

theorem bindEquivariant {x : Alloc T W A} {k : A → Alloc T W B} (hx : x.Equivariant)
    (hk : ∀ (p : Equiv.Perm T) (a : A) (t : T) (used : Set T) (b : Branch T W B),
      p • b ∈ (k (p • a)).run (p • t) (p • used) ↔ b ∈ (k a).run t used) :
    (x >>= k).Equivariant := by
  have step (p : Equiv.Perm T) (t : T) (used : Set T) (branch : Branch T W B)
      (h : branch ∈ (x >>= k).run t used) : p • branch ∈ (x >>= k).run (p • t) (p • used) := by
    rcases branch with ⟨⟨b, final⟩, w⟩
    obtain ⟨a, middle, w₁, w₂, h₁, h₂, rfl⟩ := (memAllocBind x k t used final b w).mp h
    exact (memAllocBind x k _ _ _ _ _).mpr
      ⟨p • a, p • middle, p • w₁, p • w₂, (hx p t used _).mpr h₁,
        (hk p a t middle _).mpr h₂, (smul_mul' p w₁ w₂).symm⟩
  intro p t used b
  exact ⟨fun h => by simpa only [inv_smul_smul] using step p⁻¹ _ _ _ h, step p t used b⟩

theorem mapOutputEquivariant [Monoid V] [MulDistribMulAction (Equiv.Perm T) V]
    (q : W →* V) (hq : ∀ (p : Equiv.Perm T) w, q (p • w) = p • q w)
    {x : Alloc T W A} (hx : x.Equivariant) : (Alloc.mapOutput q x).Equivariant := by
  have step (p : Equiv.Perm T) (t : T) (used : Set T) (b : Branch T V A)
      (h : b ∈ (Alloc.mapOutput q x).run t used) :
      p • b ∈ (Alloc.mapOutput q x).run (p • t) (p • used) := by
    rcases b with ⟨⟨a, final⟩, v⟩
    obtain ⟨w, hw, rfl⟩ := (memMapOutput q x t used final a v).mp h
    exact (memMapOutput q x _ _ _ _ _).mpr ⟨p • w, (hx p t used _).mpr hw, hq p w⟩
  intro p t used b
  exact ⟨fun h => by simpa only [inv_smul_smul] using step p⁻¹ _ _ _ h, step p t used b⟩

theorem representEquivariant [Monoid V] [MulDistribMulAction (Equiv.Perm T) V]
    (q : W →* V) (hq : ∀ (p : Equiv.Perm T) w, q (p • w) = p • q w)
    {x : Alloc T V A} (hx : x.Equivariant) : (Alloc.represent q x).Equivariant := by
  rintro p t used ⟨⟨a, final⟩, w⟩
  change ((p • a, p • final), q (p • w)) ∈ x.run (p • t) (p • used) ↔ _
  rw [hq]
  exact hx p t used ((a, final), q w)

theorem fixingUsed {t : T} {used : Set T} (p : fixing t used) :
    (p : Equiv.Perm T) • used = used := by
  have hp (i : T) (hi : i ∈ used) : (p : Equiv.Perm T) i = i :=
    p.2 ⟨i, Set.mem_insert_of_mem t hi⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨i, hi, rfl⟩
    change (p : Equiv.Perm T) i ∈ used
    simpa only [hp i hi] using hi
  · intro i hi
    exact ⟨i, hi, hp i hi⟩

theorem alphaEq (t : T) (used : Set T) (a b : Branch T W A) :
    alpha t used a = alpha t used b ↔ ∃ p : fixing t used, (p : Equiv.Perm T) • b = a := by
  rw [alpha, alpha, Quotient.eq'']
  exact MulAction.mem_orbit_iff

theorem alphaComplete {x : Alloc T W A} (hx : x.Equivariant) (t : T) (used : Set T) :
    alpha t used ⁻¹' (alpha t used '' x.run t used) = x.run t used := by
  ext b
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨p, rfl⟩ := (alphaEq t used b c).mp he.symm
    have ht : (p : Equiv.Perm T) • t = t := p.2 ⟨t, Set.mem_insert _ _⟩
    simpa only [ht, fixingUsed p] using
      (hx (p : Equiv.Perm T) t used c).mpr hc
  · intro hb
    exact ⟨b, hb, rfl⟩

theorem alphaUsedResult (t : T) (used : Set T) {a b : T} {s₁ s₂ : Set T} {w₁ w₂ : W}
    (ha : a ∈ used) (h : alpha t used ((a, s₁), w₁) = alpha t used ((b, s₂), w₂)) : b = a := by
  obtain ⟨p, he⟩ := (alphaEq t used _ _).mp h
  have hfix : (p : Equiv.Perm T) a = a := p.2 ⟨a, Set.mem_insert_of_mem t ha⟩
  exact (p : Equiv.Perm T).injective
    ((congrArg (fun z : Branch T W T => z.1.1) he).trans hfix.symm)

theorem freshAlpha (t : T) (used : Set T) (ht : t ∈ used) {a b : T}
    (ha : a ∉ used) (hb : b ∉ used) :
    alpha t used ((a, insert a used), (1 : W)) = alpha t used ((b, insert b used), (1 : W)) := by
  classical
  have fixed (i : T) (hi : i ∈ used) : Equiv.swap b a i = i :=
    Equiv.swap_apply_of_ne_of_ne (fun h => hb (h ▸ hi)) (fun h => ha (h ▸ hi))
  let p : fixing t used := ⟨Equiv.swap b a, (mem_fixingSubgroup_iff (Equiv.Perm T)).mpr (by
    intro i hi
    exact fixed i ((Set.insert_eq_of_mem ht) ▸ hi))⟩
  refine (alphaEq t used _ _).mpr ⟨p, ?_⟩
  have hswap : (p : Equiv.Perm T) • b = a := Equiv.swap_apply_left b a
  change (((p : Equiv.Perm T) • b, (p : Equiv.Perm T) • insert b used), (p : Equiv.Perm T) • (1 : W)) = _
  rw [Set.smul_set_insert, fixingUsed p, hswap, smul_one]

end Silmaril.Proofs.Semantics.ThreadTrace
