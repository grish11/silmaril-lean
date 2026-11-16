module

public import Silmaril.Proofs.Games.AnsPull.Zip
public import Silmaril.Proofs.Games.AnsPull.Pull
public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Games.Div.Thms
public import Silmaril.Games.Abstract.SessionRoute.Thms

/-!
# Composing with the relabelling handler below is pulling back (proofs)

`ofHandler_ansH_comp`: `(ofHandler (ansH k)).comp τ = τ.pullAns k`. Finite plays: an interaction
shows a play whose relabelling is the play of `τ`, with one call more on `τ`'s side (a prefix) or
one answer less (a play of `τ` by receptiveness) (`zip_c0`); conversely `dblL` interacts with
every play. Divergence: the handler never diverges, a divergent play of `τ` ends running so that
nothing is pending at the handler, and there is no hidden chatter, since the visible play bounds
both sides (`C0.length_le`, `zip_length_left`). Infinite plays: the upper side of an infinite
interaction grows without bound, and its limit is the relabelled visible limit; conversely the
relabelled chain of an infinite trace interacts with its doubling, whose limit is an infinite play
of the handler (`SessionRoute.ofHandler_eq_limits`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.AnsPull

open Silmaril.Games

universe u

variable {E G : Sig.{u}} {B' : E.Op → Type u} {k : (q : E.Op) → E.Ar q → B' q}

/-- **Composing with the relabelling handler below is pulling back.** -/
theorem ofHandler_ansH_comp (τ : DStrategy (Sig.mk E.Op B') G) :
    (DStrategy.ofHandler (ansH k)).comp τ = τ.pullAns k := by
  refine DStrategy.ext ?_ ?_ ?_
  · refine Strategy.ext fun p => ⟨?_, ?_⟩
    · rintro ⟨w, hw, t, ht, hz⟩
      obtain ⟨x', hx⟩ := τ.toStrategy.legal ht
      rcases zip_c0 hz hw hx with rfl | ⟨g, q, rfl, rfl⟩ | ⟨g, q, n, rfl, h⟩
      · exact ht
      · exact τ.toStrategy.of_prefix ht (List.prefix_append _ _)
      · show p.map (lowMove k) ∈ τ.toStrategy
        rw [h]
        exact τ.toStrategy.receptive ht hx
          (Step.reply (E := Sig.mk E.Op B') (F := G) g q (k q n)) trivial
    · intro hp
      have hl : Legal p := (τ.pullAns k).toStrategy.legal hp
      exact ⟨dblL k p, mem_dblL hl, p.map (lowMove k), hp, zip_dblL p⟩
  · ext p
    constructor
    · rintro (⟨w, t, hz, ⟨hw, ht⟩ | ⟨hw, ht⟩⟩ | ⟨i, hi⟩)
      · rw [DStrategy.ofHandler_div] at hw
        exact hw.elim
      · obtain ⟨g, hg⟩ := τ.div_run ht
        rcases zip_c0 hz hw hg with h | ⟨g', q, h, -⟩ | ⟨g', q, n, h, -⟩
        · show p.map (lowMove k) ∈ τ.div
          rw [← h]
          exact ht
        · cases h
        · cases h
      · exfalso
        have hb : ∀ n, (i.s n).length + (i.t n).length ≤ 3 * p.length + 2 := fun n => by
          obtain ⟨x', hx⟩ := τ.toStrategy.legal (i.mem_t n)
          have h₁ := (zip_c0 (i.zip n) (i.mem_s n) hx).length_le
          have h₂ := zip_length_left (i.zip n)
          rw [hi n] at h₁ h₂
          omega
        obtain ⟨n, hn⟩ := i.unbounded (3 * p.length + 3)
        have := hb n
        omega
    · intro hp
      have hl : Legal p := (τ.pullAns k).toStrategy.legal (τ.div_mem hp)
      exact .inl ⟨dblL k p, p.map (lowMove k), zip_dblL p, .inr ⟨mem_dblL hl, hp⟩⟩
  · ext I
    constructor
    · rintro ⟨i, hu, rfl⟩
      have hc : ∀ n, ∃ x', C0 k (i.t n) (i.p n) x' := fun n => by
        obtain ⟨x', hx⟩ := τ.toStrategy.legal (i.mem_t n)
        exact ⟨x', zip_c0 (i.zip n) (i.mem_s n) hx⟩
      have htu : i.t.Unbounded := fun j => by
        obtain ⟨n, hn⟩ := hu (j + 1)
        obtain ⟨x', h⟩ := hc n
        exact ⟨n, by have := h.length_le; omega⟩
      refine ⟨Chain.isInfPlay_lim i.mono_p hu, ?_⟩
      have hlim : List.map (lowMove k) '' i.p.lim = i.t.lim := by
        ext q
        constructor
        · rintro ⟨q, ⟨n, hq⟩, rfl⟩
          obtain ⟨m, hnm, hm⟩ := i.mono_t.unbounded_ge htu ((i.p n).length + 1) n
          have hpm : (i.p n).map (lowMove k) <+: (i.p m).map (lowMove k) :=
            (i.mono_p.le hnm).map _
          have hq' : q.map (lowMove k) <+: (i.p m).map (lowMove k) := (hq.map _).trans hpm
          obtain ⟨x', h⟩ := hc m
          refine ⟨m, ?_⟩
          rcases h with h | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩
          · rw [h]
            exact hq'
          · rw [h]
            exact hq'.trans (List.prefix_append _ _)
          · rw [h] at hq'
            refine List.prefix_of_prefix_length_le hq' (List.prefix_append _ _) ?_
            have := hq.length_le
            simp only [List.length_map]
            omega
        · rintro ⟨n, hq⟩
          obtain ⟨m, hnm, hm⟩ := i.mono_p.unbounded_ge hu (i.t n).length n
          have htm : q <+: i.t m := hq.trans (i.mono_t.le hnm)
          obtain ⟨x', h⟩ := hc m
          have hq' : q <+: (i.p m).map (lowMove k) := by
            rcases h with h | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩
            · rw [← h]
              exact htm
            · rw [h] at htm
              refine List.prefix_of_prefix_length_le htm (List.prefix_append _ _) ?_
              have := hq.length_le
              simp only [List.length_map]
              omega
            · rw [h]
              exact htm.trans (List.prefix_append _ _)
          refine ⟨(i.p m).take q.length, ⟨m, List.take_prefix _ _⟩, ?_⟩
          rw [List.map_take]
          exact (List.prefix_iff_eq_take.1 hq').symm
      show List.map (lowMove k) '' i.p.lim ∈ τ.inf
      rw [hlim]
      exact i.lim_t htu
    · rintro ⟨hJi, hJ⟩
      have hmem : ∀ n, (hJi.seq n).map (lowMove k) ∈ τ.toStrategy := fun n =>
        τ.inf_sub hJ ⟨_, hJi.seq_mem n, rfl⟩
      have hl : ∀ n, Legal (hJi.seq n) := fun n => (τ.pullAns k).toStrategy.legal (hmem n)
      have hmono_s : Chain.Mono fun n => dblL k (hJi.seq n) := fun n =>
        dblL_prefix (hJi.seq_mono n)
      refine ⟨⟨fun n => dblL k (hJi.seq n), fun n => (hJi.seq n).map (lowMove k), hJi.seq,
        fun n => zip_dblL _, fun n => mem_dblL (hl n), hmem, hmono_s,
        fun n => (hJi.seq_mono n).map _, hJi.seq_mono,
        fun j => ⟨j, by simp [hJi.seq_length]⟩, fun hu => ?_, fun _ => ?_⟩,
        fun j => ⟨j, by simp [hJi.seq_length]⟩, hJi.lim_seq.symm⟩
      · rw [Silmaril.Games.Abstract.SessionRoute.ofHandler_eq_limits]
        exact ⟨Chain.isInfPlay_lim hmono_s hu, fun q ⟨n, hq⟩ =>
          (Strategy.ofHandler (ansH k)).of_prefix (mem_dblL (hl n)) hq⟩
      · rw [lim_map, hJi.lim_seq]
        exact hJ

end Silmaril.Proofs.Games.AnsPull
