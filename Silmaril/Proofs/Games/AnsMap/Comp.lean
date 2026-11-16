module

public import Silmaril.Proofs.Games.AnsMap.Zip
public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DivLTS.Thms
public import Silmaril.Games.Div.Thms
public import Silmaril.Games.Abstract.SessionRoute.Thms

/-!
# Composing with the relabelling handler is relabelling (proofs)

`comp_ansH`: `σ.comp (ofHandler (ansH k)) = σ.mapAns k`. Finite plays: an interaction shows the
relabelled play, with one more question (a play of `σ` by receptiveness) or one answer less (a
prefix) (`zip_c0`); conversely `dblW` interacts with every play. Divergence: the handler never
diverges, a divergent play of `σ` ends running so that nothing is pending at the handler, and
there is no hidden chatter, since the visible play bounds both sides (`C0.length_le`,
`zip_length`). Infinite plays: the lower side of an infinite interaction grows without bound,
and its limit relabels to the visible limit; conversely the canonical chain of an infinite play
of `σ` interacts with its doubling, whose limit is an infinite play of the handler
(`SessionRoute.ofHandler_eq_limits`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.AnsMap

open Silmaril.Games

universe u

variable {E F : Sig.{u}} {B' : F.Op → Type u} {k : (q : F.Op) → F.Ar q → B' q}

/-- **Composing with the relabelling handler is relabelling.** -/
theorem comp_ansH (σ : DStrategy E F) : σ.comp (DStrategy.ofHandler (ansH k)) = σ.mapAns k := by
  refine DStrategy.ext ?_ ?_ ?_
  · refine Strategy.ext fun p => ⟨?_, ?_⟩
    · rintro ⟨s, hs, w, hw, hz⟩
      obtain ⟨x', hx⟩ := σ.toStrategy.legal hs
      rcases zip_c0 hz hx hw with rfl | ⟨rfl, ⟨q, rfl⟩ | ⟨o, ho⟩⟩
      · exact ⟨s, hs, rfl⟩
      · have ho : Move.IsO (.inr (.ask q) : Move E F) := trivial
        exact ⟨s ++ [.inr (.ask q)], σ.toStrategy.receptive hs hx (Step.ask (E := E) (F := F) q) ho,
          by simp [ansMove]⟩
      · refine ⟨s.take p.length, σ.toStrategy.of_prefix hs (List.take_prefix _ _), ?_⟩
        rw [List.map_take, ho]
        simp
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, dblW k q, mem_dblW (σ.toStrategy.legal hq), zip_dblW q⟩
  · ext p
    constructor
    · rintro (⟨s, w, hz, ⟨hs, hw⟩ | ⟨hs, hw⟩⟩ | ⟨i, hi⟩)
      · obtain ⟨q, hq⟩ := σ.div_run hs
        rcases zip_c0 hz hq hw with h | ⟨h, -⟩
        · exact ⟨s, hs, h.symm⟩
        · cases h
      · rw [DStrategy.ofHandler_div] at hw
        exact hw.elim
      · exfalso
        have hb : ∀ n, (i.s n).length + (i.t n).length ≤ 3 * p.length + 2 := fun n => by
          obtain ⟨x', hx⟩ := σ.toStrategy.legal (i.mem_s n)
          have h₁ := (zip_c0 (i.zip n) hx (i.mem_t n)).length_le
          have h₂ := zip_length (i.zip n)
          rw [hi n] at h₁ h₂
          omega
        obtain ⟨n, hn⟩ := i.unbounded (3 * p.length + 3)
        have := hb n
        omega
    · rintro ⟨s, hs, rfl⟩
      exact .inl ⟨s, dblW k s, zip_dblW s,
        .inl ⟨hs, mem_dblW (σ.toStrategy.legal (σ.div_mem hs))⟩⟩
  · ext I
    constructor
    · rintro ⟨i, hu, rfl⟩
      have hc : ∀ n, ∃ x', C0 k (i.s n) (i.p n) x' := fun n => by
        obtain ⟨x', hx⟩ := σ.toStrategy.legal (i.mem_s n)
        exact ⟨x', zip_c0 (i.zip n) hx (i.mem_t n)⟩
      have hsu : i.s.Unbounded := fun j => by
        obtain ⟨n, hn⟩ := hu (j + 1)
        obtain ⟨x', h⟩ := hc n
        exact ⟨n, by have := h.length_le; omega⟩
      refine ⟨i.s.lim, i.lim_s hsu, ?_⟩
      ext q
      constructor
      · rintro ⟨n, hq⟩
        obtain ⟨m, hnm, hm⟩ := i.mono_s.unbounded_ge hsu (i.p n).length n
        have hpm : i.p n <+: i.p m := i.mono_p.le hnm
        obtain ⟨x', h⟩ := hc m
        have : i.p n <+: (i.s m).map (ansMove k) := by
          rcases h with h | ⟨-, ⟨a, h⟩ | ⟨o, h⟩⟩
          · rw [← h]
            exact hpm
          · rw [h] at hpm
            exact List.prefix_of_prefix_length_le hpm (List.prefix_append _ _) (by simp; omega)
          · rw [h]
            exact hpm.trans (List.prefix_append _ _)
        have hq' := hq.trans this
        refine ⟨(i.s m).take q.length, ⟨m, List.take_prefix _ _⟩, ?_⟩
        rw [List.map_take]
        exact (List.prefix_iff_eq_take.1 hq').symm
      · rintro ⟨q', ⟨n, hq'⟩, rfl⟩
        obtain ⟨m, hnm, hm⟩ := i.mono_p.unbounded_ge hu (i.s n).length n
        have hsm : (i.s n).map (ansMove k) <+: (i.s m).map (ansMove k) := (i.mono_s.le hnm).map _
        obtain ⟨x', h⟩ := hc m
        have : (i.s n).map (ansMove k) <+: i.p m := by
          rcases h with h | ⟨-, ⟨a, h⟩ | ⟨o, h⟩⟩
          · rw [h]
            exact hsm
          · rw [h]
            exact hsm.trans (List.prefix_append _ _)
          · rw [h] at hsm
            exact List.prefix_of_prefix_length_le hsm (List.prefix_append _ _) (by simp; omega)
        exact ⟨m, (hq'.map _).trans this⟩
    · rintro ⟨J, hJ, rfl⟩
      have hJi := σ.inf_isInf hJ
      have hmem : ∀ n, hJi.seq n ∈ σ.toStrategy := fun n => σ.inf_sub hJ (hJi.seq_mem n)
      have hmono_t : Chain.Mono fun n => dblW k (hJi.seq n) := fun n => dblW_prefix (hJi.seq_mono n)
      refine ⟨⟨hJi.seq, fun n => dblW k (hJi.seq n), fun n => (hJi.seq n).map (ansMove k),
        fun n => zip_dblW _, hmem, fun n => mem_dblW (σ.toStrategy.legal (hmem n)), hJi.seq_mono,
        hmono_t, fun n => (hJi.seq_mono n).map _,
        fun j => ⟨j, by simp [hJi.seq_length]⟩, fun _ => by rw [hJi.lim_seq]; exact hJ,
        fun hu => ?_⟩, fun j => ⟨j, by simp [hJi.seq_length]⟩, ?_⟩
      · rw [Silmaril.Games.Abstract.SessionRoute.ofHandler_eq_limits]
        exact ⟨Chain.isInfPlay_lim hmono_t hu, fun q ⟨n, hq⟩ =>
          (Strategy.ofHandler (ansH k)).of_prefix (mem_dblW (σ.toStrategy.legal (hmem n))) hq⟩
      · ext q
        constructor
        · rintro ⟨q', hq', rfl⟩
          rw [← hJi.lim_seq] at hq'
          obtain ⟨n, hn⟩ := hq'
          exact ⟨n, hn.map _⟩
        · rintro ⟨n, hn⟩
          refine ⟨(hJi.seq n).take q.length, hJi.of_prefix (hJi.seq_mem n) (List.take_prefix _ _),
            ?_⟩
          rw [List.map_take]
          exact (List.prefix_iff_eq_take.1 hn).symm

end Silmaril.Proofs.Games.AnsMap
