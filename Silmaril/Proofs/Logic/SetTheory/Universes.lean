module

public import Silmaril.Logic.SetTheory.Universes.Defs

/-! Proofs of universe closure and the embedding construction. -/

public section

namespace Silmaril.Proofs.Logic.SetTheory

universe u v

open ZFSet Silmaril.Logic.SetTheory

theorem mem_liftSet {x : ZFSet.{u}} {y : ZFSet.{max u v}} :
    y ∈ liftSet.{u, v} x ↔ ∃ z ∈ x, liftSet z = y := by
  rw [liftSet]
  refine (@mem_range _ (small_lift.{u + 1, v, u} _) _ _).trans
    ⟨fun ⟨z, h⟩ => ⟨z.1, z.2, h⟩, fun ⟨z, hz, h⟩ => ⟨⟨z, hz⟩, h⟩⟩

theorem liftSet_mem_liftSet {x y : ZFSet.{u}} (h : x ∈ y) : liftSet.{u, v} x ∈ liftSet y :=
  mem_liftSet.2 ⟨x, h, rfl⟩

theorem liftSet_injective : Function.Injective liftSet.{u, v} := by
  intro x
  induction x using ZFSet.inductionOn with | h x ih =>
  intro y hxy
  ext z
  constructor
  · intro hz
    have hz' : liftSet.{u, v} z ∈ liftSet x := liftSet_mem_liftSet hz
    obtain ⟨w, hw, e⟩ := mem_liftSet.1 (hxy ▸ hz')
    exact (ih z hz e.symm) ▸ hw
  · intro hz
    have hz' : liftSet.{u, v} z ∈ liftSet y := liftSet_mem_liftSet hz
    obtain ⟨w, hw, e⟩ := mem_liftSet.1 (hxy.symm ▸ hz')
    exact (ih w hw e) ▸ hw

@[simp] theorem liftSet_inj {x y : ZFSet.{u}} : liftSet.{u, v} x = liftSet y ↔ x = y :=
  liftSet_injective.eq_iff

@[simp] theorem liftSet_mem_liftSet_iff {x y : ZFSet.{u}} :
    liftSet.{u, v} x ∈ liftSet y ↔ x ∈ y := by
  rw [mem_liftSet]
  exact ⟨fun ⟨z, hz, e⟩ => liftSet_injective e ▸ hz, fun h => ⟨x, h, rfl⟩⟩

theorem liftSet_insert (x y : ZFSet.{u}) :
    liftSet.{u, v} (insert x y) = insert (liftSet x) (liftSet y) := by
  ext z
  simp only [mem_liftSet, mem_insert_iff]
  constructor
  · rintro ⟨a, rfl | ha, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨a, ha, rfl⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨x, .inl rfl, rfl⟩
    · exact ⟨a, .inr ha, rfl⟩

theorem liftSet_empty : liftSet.{u, v} ∅ = ∅ := by
  ext z
  simp [mem_liftSet]

theorem liftSet_singleton (x : ZFSet.{u}) : liftSet.{u, v} {x} = {liftSet.{u, v} x} := by
  apply ZFSet.ext
  intro z
  simp [mem_liftSet, eq_comm]

theorem liftSet_orderedPair (x y : ZFSet.{u}) :
    liftSet.{u, v} (ZFSet.pair x y) = ZFSet.pair (liftSet.{u, v} x) (liftSet.{u, v} y) := by
  simp only [ZFSet.pair, liftSet_insert, liftSet_singleton]

theorem liftSet_numeral (n : ℕ) : liftSet.{u, v} (Silmaril.Logic.SetTheory.numeral n) = Silmaril.Logic.SetTheory.numeral n := by
  induction n with
  | zero => exact liftSet_empty
  | succ n ih => rw [Silmaril.Logic.SetTheory.numeral_succ, Silmaril.Logic.SetTheory.numeral_succ, Silmaril.Logic.SetTheory.succ, Silmaril.Logic.SetTheory.succ, liftSet_insert, ih]

theorem liftSet_omega : liftSet.{u, v} omega = omega := by
  ext z
  rw [mem_liftSet, Silmaril.Logic.SetTheory.mem_omega_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, rfl⟩ := Silmaril.Logic.SetTheory.mem_omega_iff.1 ha
    exact ⟨n, (liftSet_numeral n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨Silmaril.Logic.SetTheory.numeral n, Silmaril.Logic.SetTheory.numeral_mem_omega n, liftSet_numeral n⟩

theorem liftSet_sUnion (x : ZFSet.{u}) : liftSet.{u, v} (⋃₀ x) = ⋃₀ liftSet x := by
  ext z
  simp only [mem_liftSet, mem_sUnion]
  constructor
  · rintro ⟨a, ⟨b, hb, ha⟩, rfl⟩
    exact ⟨liftSet b, ⟨b, hb, rfl⟩, liftSet_mem_liftSet ha⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, hz⟩
    obtain ⟨a, ha, rfl⟩ := mem_liftSet.1 hz
    exact ⟨a, ⟨b, hb, ha⟩, rfl⟩


/-- The copy of a set is `u`-small. -/
theorem small_liftSet (x : ZFSet.{u}) : Small.{u} (liftSet.{u, v} x) :=
  small_of_surjective (f := fun y : x => (⟨liftSet y.1, liftSet_mem_liftSet y.2⟩ : liftSet x))
    fun ⟨_, hz⟩ => by
      obtain ⟨a, ha, rfl⟩ := mem_liftSet.1 hz
      exact ⟨⟨a, ha⟩, rfl⟩

theorem mem_mk_iff_exists {α : Type u} {A : α → PSet.{u}} {w : ZFSet.{u}} :
    w ∈ ZFSet.mk ⟨α, A⟩ ↔ ∃ a, ZFSet.mk (A a) = w := by
  induction w using Quotient.inductionOn with | h r =>
  rw [mk_eq, mk_mem_iff, PSet.mem_def]
  exact exists_congr fun a => ⟨fun h => (ZFSet.sound h).symm, fun h => (ZFSet.exact h).symm⟩

/-- `liftSet` is Mathlib's `PSet.Lift` on representatives. -/
theorem liftSet_mk (p : PSet.{u}) :
    liftSet.{u, v} (ZFSet.mk p) = ZFSet.mk (PSet.Lift.{u, v} p) := by
  induction p with | mk α A ih =>
  ext z
  rw [mem_liftSet, PSet.Lift, mem_mk_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := mem_mk_iff_exists.1 hw
    exact ⟨⟨a⟩, (ih a).symm⟩
  · rintro ⟨⟨a⟩, rfl⟩
    exact ⟨ZFSet.mk (A a), mem_mk_iff_exists.2 ⟨a, rfl⟩, ih a⟩

/-! ### The universe of lifted sets -/


theorem mem_universeSet {x : ZFSet.{u + 1}} : x ∈ universeSet ↔ ∃ a, liftSet.{u, u + 1} a = x :=
  mem_range

theorem liftSet_mem_universeSet (a : ZFSet.{u}) : liftSet.{u, u + 1} a ∈ universeSet :=
  mem_universeSet.2 ⟨a, rfl⟩

/-- `universeSet` is the class of Mathlib's `PSet.embed`. -/
theorem universeSet_eq_mk_embed : universeSet.{u} = ZFSet.mk PSet.embed.{u, u + 1} := by
  ext z
  rw [mem_universeSet, PSet.embed, mem_mk_iff_exists]
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn with | h p =>
    exact ⟨⟨p⟩, (liftSet_mk p).symm⟩
  · rintro ⟨⟨p⟩, rfl⟩
    exact ⟨ZFSet.mk p, liftSet_mk p⟩

theorem universeSet_isTransitive : universeSet.{u}.IsTransitive := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_universeSet.1 hx
  obtain ⟨b, -, rfl⟩ := mem_liftSet.1 hy
  exact liftSet_mem_universeSet b

/-- A subset of the universe belongs to it exactly when it is `u`-small. -/
theorem mem_universeSet_iff_small {z : ZFSet.{u + 1}} (hz : z ⊆ universeSet) :
    z ∈ universeSet ↔ Small.{u} z := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := mem_universeSet.1 h
    exact small_liftSet a
  · intro h
    let S := {a : ZFSet.{u} // liftSet.{u, u + 1} a ∈ z}
    have : Small.{u} S := small_of_injective (f := fun s : S => (⟨_, s.2⟩ : z))
      fun s t hst => Subtype.ext (liftSet_injective (congrArg Subtype.val hst))
    refine mem_universeSet.2 ⟨range (Subtype.val : S → ZFSet.{u}), ?_⟩
    ext t
    rw [mem_liftSet]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨s, rfl⟩ := mem_range.1 ha
      exact s.2
    · intro ht
      obtain ⟨a, rfl⟩ := mem_universeSet.1 (hz ht)
      exact ⟨a, mem_range.2 ⟨⟨a, ht⟩, rfl⟩, rfl⟩


theorem liftSet_pair (x y : ZFSet.{u}) :
    liftSet.{u, v} {x, y} = {liftSet x, liftSet y} := by
  ext z
  simp only [mem_liftSet, mem_pair, or_and_right, exists_or, exists_eq_left]
  exact or_congr eq_comm eq_comm

theorem liftSet_powerset (a : ZFSet.{u}) :
    liftSet.{u, v} (powerset a) = powerset (liftSet a) := by
  ext w
  rw [mem_liftSet, mem_powerset]
  constructor
  · rintro ⟨b, hb, rfl⟩ t ht
    obtain ⟨c, hc, rfl⟩ := mem_liftSet.1 ht
    exact liftSet_mem_liftSet (mem_powerset.1 hb hc)
  · intro h
    refine ⟨ZFSet.sep (fun c => liftSet.{u, v} c ∈ w) a,
      mem_powerset.2 fun c hc => (mem_sep.1 hc).1, ?_⟩
    ext t
    rw [mem_liftSet]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (mem_sep.1 hc).2
    · intro ht
      obtain ⟨c, hc, rfl⟩ := mem_liftSet.1 (h ht)
      exact ⟨c, mem_sep.2 ⟨hc, ht⟩, rfl⟩

theorem small_of_mem_universeSet {x : ZFSet.{u + 1}} (h : x ∈ universeSet) : Small.{u} x :=
  (mem_universeSet_iff_small (universeSet_isTransitive.subset_of_mem h)).1 h

theorem omega_mem_universeSet : (omega : ZFSet.{u + 1}) ∈ universeSet.{u} :=
  liftSet_omega.{u, u + 1} ▸ liftSet_mem_universeSet omega

/-- The universe is a Grothendieck universe. -/
theorem isGrothendieckUniverse_universeSet : IsGrothendieckUniverse universeSet.{u} where
  isTransitive := universeSet_isTransitive
  pair_mem x hx y hy := by
    obtain ⟨a, rfl⟩ := mem_universeSet.1 hx
    obtain ⟨b, rfl⟩ := mem_universeSet.1 hy
    exact liftSet_pair a b ▸ liftSet_mem_universeSet _
  powerset_mem x hx := by
    obtain ⟨a, rfl⟩ := mem_universeSet.1 hx
    exact liftSet_powerset a ▸ liftSet_mem_universeSet _
  iUnion_mem x hx f hf := by
    have hsub : (⋃ i, f i) ⊆ universeSet := fun t ht => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 ht
      exact universeSet_isTransitive _ (hf i) hi
    refine (mem_universeSet_iff_small hsub).2 ?_
    have := small_of_mem_universeSet hx
    have := fun i => small_of_mem_universeSet (hf i)
    refine small_of_surjective (f := fun p : Σ i : x, f i =>
      (⟨p.2.1, mem_iUnion.2 ⟨p.1, p.2.2⟩⟩ : (⋃ i, f i : ZFSet.{u + 1}))) fun ⟨t, ht⟩ => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 ht
    exact ⟨⟨i, t, hi⟩, rfl⟩
  omega_mem := omega_mem_universeSet


namespace IsGrothendieckUniverse

variable {U x y : ZFSet.{u}} (h : Silmaril.Logic.SetTheory.IsGrothendieckUniverse U)
include h

/-- Every Grothendieck universe contains the empty set. -/
theorem empty_mem : (∅ : ZFSet.{u}) ∈ U :=
  h.isTransitive omega h.omega_mem omega_zero

/-- A subset of a member of a universe belongs to the universe. -/
theorem subset_mem (hy : y ∈ U) (hxy : x ⊆ y) : x ∈ U :=
  h.isTransitive (powerset y) (h.powerset_mem y hy) (mem_powerset.2 hxy)

/-- A singleton of a member belongs to the universe. -/
theorem singleton_mem (hx : x ∈ U) : ({x} : ZFSet.{u}) ∈ U := by
  simpa only [pair_eq_singleton] using h.pair_mem x hx x hx

/-- A union indexed by a member of the universe belongs to it. -/
theorem sUnion_mem (hx : x ∈ U) : (⋃₀ x) ∈ U := by
  have hi := h.iUnion_mem x hx (fun i => i.1)
    (fun i => h.isTransitive x hx i.2)
  have he : (⋃ i : x, i.1) = ⋃₀ x := by
    ext z
    simp only [mem_iUnion, mem_sUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨i.1, i.2, hi⟩, fun ⟨y, hy, hz⟩ => ⟨⟨y, hy⟩, hz⟩⟩
  exact he ▸ hi

theorem union_mem (hx : x ∈ U) (hy : y ∈ U) : x ∪ y ∈ U := by
  simpa only [sUnion_pair] using sUnion_mem h (h.pair_mem x hx y hy)

theorem insert_mem (hx : x ∈ U) (hy : y ∈ U) : insert x y ∈ U := by
  rw [insert_eq]
  exact union_mem h (singleton_mem h hx) hy

/-- Kuratowski pairs of members belong to the universe. -/
theorem opair_mem (hx : x ∈ U) (hy : y ∈ U) : ZFSet.pair x y ∈ U :=
  h.pair_mem _ (singleton_mem h hx) _ (h.pair_mem x hx y hy)

/-- Images of a member by a universe-valued function belong to the universe. -/
theorem range_mem (hx : x ∈ U) (f : x → ZFSet.{u}) (hf : ∀ i, f i ∈ U) :
    ZFSet.range f ∈ U := by
  have hi := h.iUnion_mem x hx (fun i => {f i}) (fun i => singleton_mem h (hf i))
  have he : (⋃ i : x, ({f i} : ZFSet.{u})) = ZFSet.range f := by
    ext z
    simp only [mem_iUnion, mem_singleton, mem_range]
    exact exists_congr fun _ => eq_comm
  exact he ▸ hi

/-- Cartesian products of members belong to the universe. -/
theorem prod_mem (hx : x ∈ U) (hy : y ∈ U) : ZFSet.prod x y ∈ U := by
  exact subset_mem h
    (h.powerset_mem _ (h.powerset_mem _ (union_mem h hx hy)))
    (by
      intro z hz
      unfold ZFSet.prod ZFSet.pairSep at hz
      exact (mem_sep.1 hz).1)

/-- Lifting a universe preserves its closure properties. -/
theorem liftSet : Silmaril.Logic.SetTheory.IsGrothendieckUniverse
    (Silmaril.Logic.SetTheory.liftSet.{u, v} U) where
  isTransitive := by
    intro x hx y hy
    obtain ⟨a, ha, hax⟩ := mem_liftSet.1 hx
    have hy' : y ∈ Silmaril.Logic.SetTheory.liftSet.{u, v} a := hax.symm ▸ hy
    obtain ⟨b, hb, hby⟩ := mem_liftSet.1 hy'
    exact hby ▸ liftSet_mem_liftSet (h.isTransitive a ha hb)
  pair_mem := by
    intro x hx y hy
    obtain ⟨a, ha, hax⟩ := mem_liftSet.1 hx
    obtain ⟨b, hb, hby⟩ := mem_liftSet.1 hy
    have hab : Silmaril.Logic.SetTheory.liftSet.{u, v} ({a, b} : ZFSet.{u}) ∈
        Silmaril.Logic.SetTheory.liftSet.{u, v} U :=
      liftSet_mem_liftSet (h.pair_mem a ha b hb)
    simpa only [liftSet_pair, hax, hby] using hab
  powerset_mem := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := mem_liftSet.1 hx
    have ha' : Silmaril.Logic.SetTheory.liftSet.{u, v} (powerset a) ∈
        Silmaril.Logic.SetTheory.liftSet.{u, v} U :=
      liftSet_mem_liftSet (h.powerset_mem a ha)
    simpa only [liftSet_powerset, hax] using ha'
  iUnion_mem := by
    intro x hx f hf
    obtain ⟨a, ha, hax⟩ := mem_liftSet.1 hx
    let e (i : a) : x := ⟨_, hax ▸ liftSet_mem_liftSet i.2⟩
    have he : Function.Surjective e := by
      intro j
      have hj : j.1 ∈ Silmaril.Logic.SetTheory.liftSet.{u, v} a := hax.symm ▸ j.2
      obtain ⟨b, hb, hbj⟩ := mem_liftSet.1 hj
      exact ⟨⟨b, hb⟩, Subtype.ext hbj⟩
    let g (i : a) : ZFSet.{u} := (mem_liftSet.1 (hf (e i))).choose
    have hg (i : a) : g i ∈ U ∧ Silmaril.Logic.SetTheory.liftSet.{u, v} (g i) = f (e i) :=
      (mem_liftSet.1 (hf (e i))).choose_spec
    have hi : Silmaril.Logic.SetTheory.liftSet.{u, v} (⋃ i, g i) ∈
        Silmaril.Logic.SetTheory.liftSet.{u, v} U :=
      liftSet_mem_liftSet (h.iUnion_mem a ha g (fun i => (hg i).1))
    have hiu : Silmaril.Logic.SetTheory.liftSet.{u, v} (⋃ i, g i) = ⋃ i, f i := by
      ext z
      rw [mem_liftSet, mem_iUnion]
      constructor
      · rintro ⟨w, hw, hwz⟩
        obtain ⟨i, hi⟩ := mem_iUnion.1 hw
        exact ⟨e i, (hg i).2 ▸ (hwz ▸ liftSet_mem_liftSet hi)⟩
      · rintro ⟨j, hj⟩
        obtain ⟨i, hij⟩ := he j
        have hj' : z ∈ Silmaril.Logic.SetTheory.liftSet.{u, v} (g i) :=
          (hg i).2.symm ▸ (hij.symm ▸ hj)
        obtain ⟨w, hw, hwz⟩ := mem_liftSet.1 hj'
        exact ⟨w, mem_iUnion.2 ⟨i, hw⟩, hwz⟩
    exact hiu ▸ hi
  omega_mem := by
    rw [← liftSet_omega.{u, v}]
    exact liftSet_mem_liftSet h.omega_mem

end IsGrothendieckUniverse

end Silmaril.Proofs.Logic.SetTheory
