module

public import Silmaril.Wasm.Component.DWiringChatter3.Defs
public import Silmaril.Games.Div.Thms

/-!
# Infinite plays of a composite, without chains

An infinite play of `σ.comp τ` is the visible limit of an infinite interaction
`i : InfInteraction σ τ`. Here the chains of `i` are replaced by their limits
(`inf_comp_eq`): the visible limit `J` is an infinite trace, the limits of the
two sides are runs of `σ` and `τ` (`IsRun`: an infinite play when the side
moves forever, the prefixes of a finite play when it stops), and the three
limits are `Interleaved`.

Forwards, a bounded increasing chain is eventually constant, so its limit is the
prefixes of a play. Backwards, the interacting triples are chosen by dependent
choice, each extending the previous one and the members of each length of the
three traces (`tri`), so that their limits are the given traces.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringChatter3

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Games.DStrategy (InfInteraction)

universe u v w

/-! ## Traces -/

section Trace

variable {α : Type u}

/-- A trace: prefix closed, totally ordered by the prefix order, nonempty. -/
structure IsTrace (I : Set (List α)) : Prop where
  nil_mem : [] ∈ I
  of_prefix : ∀ {s t}, t ∈ I → s <+: t → s ∈ I
  total : ∀ {s t}, s ∈ I → t ∈ I → s <+: t ∨ t <+: s

theorem IsTrace.prefix_of_length_le {I : Set (List α)} (h : IsTrace I) {s t : List α}
    (hs : s ∈ I) (ht : t ∈ I) (hl : s.length ≤ t.length) : s <+: t := by
  rcases h.total hs ht with h' | h'
  · exact h'
  · obtain rfl := h'.eq_of_length (le_antisymm h'.length_le hl)
    exact List.prefix_refl _

theorem isTrace_of_isInfPlay {I : Set (List α)} (h : IsInfPlay I) : IsTrace I := by
  obtain ⟨s, hs, -⟩ := h.unbounded 0
  exact ⟨h.of_prefix hs List.nil_prefix, h.of_prefix, h.total⟩

theorem isTrace_prefixes (s : List α) : IsTrace (prefixes s) :=
  ⟨List.nil_prefix, fun ht hst => hst.trans ht, fun hs ht => List.prefix_or_prefix_of_prefix hs ht⟩

theorem not_isInfPlay_prefixes (s : List α) : ¬ IsInfPlay (prefixes s) := by
  intro h
  obtain ⟨t, ht, hl⟩ := h.unbounded (s.length + 1)
  have := List.IsPrefix.length_le ht
  omega

/-- The longer of two lists. -/
def up (x y : List α) : List α := if x.length ≤ y.length then y else x

theorem up_mem {I : Set (List α)} {x y : List α} (hx : x ∈ I) (hy : y ∈ I) : up x y ∈ I := by
  unfold up; split_ifs <;> assumption

theorem le_up_left {I : Set (List α)} (h : IsTrace I) {x y : List α} (hx : x ∈ I) (hy : y ∈ I) :
    x <+: up x y := by
  unfold up; split_ifs with hl
  · exact h.prefix_of_length_le hx hy hl
  · exact List.prefix_refl _

theorem le_up_right {I : Set (List α)} (h : IsTrace I) {x y : List α} (hx : x ∈ I) (hy : y ∈ I) :
    y <+: up x y := by
  unfold up; split_ifs with hl
  · exact List.prefix_refl _
  · exact h.prefix_of_length_le hy hx (by omega)

open Classical in
/-- A member of `I` of length at least `n`, if there is one. -/
noncomputable def tgt (I : Set (List α)) (n : ℕ) : List α :=
  if h : ∃ x ∈ I, n ≤ x.length then h.choose else []

theorem tgt_mem {I : Set (List α)} (h : IsTrace I) (n : ℕ) : tgt I n ∈ I := by
  unfold tgt; split_ifs with hn
  · exact hn.choose_spec.1
  · exact h.nil_mem

theorem le_tgt {I : Set (List α)} (h : IsTrace I) {x : List α} (hx : x ∈ I) :
    x <+: tgt I x.length := by
  have hn : ∃ y ∈ I, x.length ≤ y.length := ⟨x, hx, le_rfl⟩
  unfold tgt; split_ifs
  exact h.prefix_of_length_le hx hn.choose_spec.1 hn.choose_spec.2

theorem length_tgt {I : Set (List α)} (h : IsInfPlay I) (n : ℕ) : n ≤ (tgt I n).length := by
  have hn : ∃ y ∈ I, n ≤ y.length := h.unbounded n
  unfold tgt; split_ifs
  exact hn.choose_spec.2

/-- A chain in a trace reaching beyond each member of each length has the trace
as limit. -/
theorem lim_eq_of_tgt {I : Set (List α)} (h : IsTrace I) {c : Chain α} (hmem : ∀ n, c n ∈ I)
    (hc : ∀ n, tgt I n <+: c (n + 1)) : c.lim = I := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    exact h.of_prefix (hmem n) hn
  · intro hx
    exact ⟨x.length + 1, (le_tgt h hx).trans (hc _)⟩

end Trace

/-! ## Interacting triples -/

section Zip

variable {α : Type u} {β : Type v} {γ : Type w}

theorem zip_length {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    p.length ≤ s.length + t.length := by
  induction h with
  | nil => simp
  | left _ _ ih => simp; omega
  | right _ _ ih => simp; omega
  | sync _ _ ih => simp; omega

/-- A triple of members of `I`, `K` and `J` that interact. -/
def Good (I : Set (List (α ⊕ β))) (K : Set (List (β ⊕ γ))) (J : Set (List (α ⊕ γ)))
    (x : List (α ⊕ β) × List (β ⊕ γ) × List (α ⊕ γ)) : Prop :=
  x.1 ∈ I ∧ x.2.1 ∈ K ∧ x.2.2 ∈ J ∧ Zip x.1 x.2.1 x.2.2

variable {I : Set (List (α ⊕ β))} {K : Set (List (β ⊕ γ))} {J : Set (List (α ⊕ γ))}

theorem exists_good (h : Interleaved I K J) {a b d} (ha : a ∈ I) (hb : b ∈ K) (hd : d ∈ J) :
    ∃ y, Good I K J y ∧ a <+: y.1 ∧ b <+: y.2.1 ∧ d <+: y.2.2 := by
  obtain ⟨s, hs, c, hc, p, hp, h₁, h₂, h₃, hz⟩ := h a ha b hb d hd
  exact ⟨(s, c, p), ⟨hs, hc, hp, hz⟩, h₁, h₂, h₃⟩

/-- The next interacting triple: beyond the current one and the members of
length `n`. -/
noncomputable def next (h : Interleaved I K J) (hI : IsTrace I) (hK : IsTrace K) (hJ : IsTrace J)
    (n : ℕ) (x : {x // Good I K J x}) : {x // Good I K J x} :=
  ⟨_, (exists_good h (up_mem x.2.1 (tgt_mem hI n)) (up_mem x.2.2.1 (tgt_mem hK n))
    (up_mem x.2.2.2.1 (tgt_mem hJ n))).choose_spec.1⟩

/-- The chain of interacting triples. -/
noncomputable def tri (h : Interleaved I K J) (hI : IsTrace I) (hK : IsTrace K) (hJ : IsTrace J) :
    ℕ → {x // Good I K J x}
  | 0 => ⟨([], [], []), hI.nil_mem, hK.nil_mem, hJ.nil_mem, .nil⟩
  | n + 1 => next h hI hK hJ n (tri h hI hK hJ n)

theorem tri_succ (h : Interleaved I K J) (hI : IsTrace I) (hK : IsTrace K) (hJ : IsTrace J)
    (n : ℕ) :
    let x := (tri h hI hK hJ n).1
    let y := (tri h hI hK hJ (n + 1)).1
    (x.1 <+: y.1 ∧ tgt I n <+: y.1) ∧ (x.2.1 <+: y.2.1 ∧ tgt K n <+: y.2.1) ∧
      (x.2.2 <+: y.2.2 ∧ tgt J n <+: y.2.2) := by
  intro x y
  have hx := (tri h hI hK hJ n).2
  obtain ⟨-, h₁, h₂, h₃⟩ := (exists_good h (up_mem hx.1 (tgt_mem hI n))
    (up_mem hx.2.1 (tgt_mem hK n)) (up_mem hx.2.2.1 (tgt_mem hJ n))).choose_spec
  exact ⟨⟨(le_up_left hI hx.1 (tgt_mem hI n)).trans h₁, (le_up_right hI hx.1 (tgt_mem hI n)).trans h₁⟩,
    ⟨(le_up_left hK hx.2.1 (tgt_mem hK n)).trans h₂, (le_up_right hK hx.2.1 (tgt_mem hK n)).trans h₂⟩,
    ⟨(le_up_left hJ hx.2.2.1 (tgt_mem hJ n)).trans h₃,
      (le_up_right hJ hx.2.2.1 (tgt_mem hJ n)).trans h₃⟩⟩

end Zip

/-! ## Runs -/

section Runs

variable {E F G : Sig.{u}}

theorem IsRun.isTrace {δ : DStrategy E F} {I : Set (List (Move E F))} (h : IsRun δ I) :
    IsTrace I := by
  rcases h with h | ⟨s, -, rfl⟩
  · exact isTrace_of_isInfPlay (δ.inf_isInf h)
  · exact isTrace_prefixes s

theorem IsRun.subset {δ : DStrategy E F} {I : Set (List (Move E F))} (h : IsRun δ I) :
    I ⊆ δ.toStrategy.plays := by
  rcases h with h | ⟨s, hs, rfl⟩
  · exact δ.inf_sub h
  · exact fun t ht => δ.toStrategy.of_prefix hs ht

/-- The limit of an increasing chain of plays is a run. -/
theorem isRun_lim {δ : DStrategy E F} {c : Chain (Move E F)} (hm : c.Mono)
    (hmem : ∀ n, c n ∈ δ.toStrategy) (hl : c.Unbounded → c.lim ∈ δ.inf) : IsRun δ c.lim := by
  by_cases hu : c.Unbounded
  · exact .inl (hl hu)
  · obtain ⟨N, hN⟩ := hm.eventually_const hu
    refine .inr ⟨c N, hmem N, ?_⟩
    ext q
    constructor
    · rintro ⟨n, hn⟩
      rcases le_total n N with h | h
      · exact hn.trans (hm.le h)
      · rwa [hN n h] at hn
    · exact fun h => ⟨N, h⟩

/-- **Infinite plays of a composite, without chains.** -/
theorem inf_comp_eq (σ : DStrategy E F) (τ : DStrategy F G) :
    (σ.comp τ).inf = {J | IsInfPlay J ∧ ∃ I K, IsRun σ I ∧ IsRun τ K ∧ Interleaved I K J} := by
  ext J
  constructor
  · rintro ⟨i, hu, rfl⟩
    refine ⟨Chain.isInfPlay_lim i.mono_p hu, i.s.lim, i.t.lim,
      isRun_lim i.mono_s i.mem_s i.lim_s, isRun_lim i.mono_t i.mem_t i.lim_t, ?_⟩
    rintro s ⟨a, ha⟩ c ⟨b, hb⟩ p ⟨d, hd⟩
    refine ⟨_, Chain.mem_lim_self _ (a + b + d), _, Chain.mem_lim_self _ (a + b + d),
      _, Chain.mem_lim_self _ (a + b + d), ha.trans (i.mono_s.le (by omega)),
      hb.trans (i.mono_t.le (by omega)), hd.trans (i.mono_p.le (by omega)), i.zip _⟩
  · rintro ⟨hJ, I, K, hIr, hKr, hint⟩
    have hI := IsRun.isTrace hIr
    have hK := IsRun.isTrace hKr
    have hJt := isTrace_of_isInfPlay hJ
    let x := tri hint hI hK hJt
    have hs := fun n => tri_succ hint hI hK hJt n
    have hmono_s : Chain.Mono fun n => (x n).1.1 := fun n => (hs n).1.1
    have hmono_t : Chain.Mono fun n => (x n).1.2.1 := fun n => (hs n).2.1.1
    have hmono_p : Chain.Mono fun n => (x n).1.2.2 := fun n => (hs n).2.2.1
    have hlimI : Chain.lim (fun n => (x n).1.1) = I :=
      lim_eq_of_tgt hI (fun n => (x n).2.1) fun n => (hs n).1.2
    have hlimK : Chain.lim (fun n => (x n).1.2.1) = K :=
      lim_eq_of_tgt hK (fun n => (x n).2.2.1) fun n => (hs n).2.1.2
    have hlimJ : Chain.lim (fun n => (x n).1.2.2) = J :=
      lim_eq_of_tgt hJt (fun n => (x n).2.2.2.1) fun n => (hs n).2.2.2
    have hpu : Chain.Unbounded fun n => (x n).1.2.2 :=
      fun k => ⟨k + 1, (length_tgt hJ k).trans ((hs k).2.2.2.length_le)⟩
    have hrun : ∀ {E F : Sig.{u}} {δ : DStrategy E F} {I : Set (List (Move E F))}
        {c : Chain (Move E F)}, IsRun δ I → c.lim = I → c.Unbounded → c.lim ∈ δ.inf := by
      intro E F δ I c hr hl hu
      rcases hr with hr | ⟨s₀, -, rfl⟩
      · rwa [hl]
      · obtain ⟨n, hn⟩ := hu (s₀.length + 1)
        have : c n ∈ prefixes s₀ := hl ▸ Chain.mem_lim_self c n
        have : c n <+: s₀ := this
        have := this.length_le
        omega
    refine ⟨⟨fun n => (x n).1.1, fun n => (x n).1.2.1, fun n => (x n).1.2.2, fun n => (x n).2.2.2.2,
      fun n => IsRun.subset hIr (x n).2.1, fun n => IsRun.subset hKr (x n).2.2.1, hmono_s, hmono_t, hmono_p,
      fun k => ?_, fun hu => hrun hIr hlimI hu, fun hu => hrun hKr hlimK hu⟩, hpu, hlimJ.symm⟩
    obtain ⟨n, hn⟩ := hpu k
    exact ⟨n, hn.trans (zip_length (x n).2.2.2.2)⟩

end Runs

end Silmaril.Proofs.Wasm.Component.DWiringChatter3
