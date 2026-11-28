module

public import Silmaril.Logic.Temporal.TLA.Rules.Figure5.Temporal.Defs
public import Silmaril.Logic.Temporal.TLA.Thms

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.Rules.Figure5

open Silmaril.Logic.Temporal.TLA
open Silmaril.Logic.Temporal.TLA.Rules.Figure5
open Formula

universe u v

variable {S : Type u} {ι : Type v}

private theorem holdsWith {Γ : List (Formula S)} {F : Formula S} {σ : Behavior S} {i : Nat}
    (valid : ∀ G ∈ Γ, G.Holds σ i) (hF : F.Holds σ i) : ∀ G ∈ F :: Γ, G.Holds σ i := by
  intro G member
  rcases List.mem_cons.mp member with rfl | member
  · exact hF
  · exact valid G member

theorem propDerives_sound {Γ : List (Formula S)} {F : Formula S} (proof : PropDerives Γ F)
    (σ : Behavior S) (i : Nat) (valid : ∀ G ∈ Γ, G.Holds σ i) : F.Holds σ i := by
  induction proof with
  | hyp member => exact valid _ member
  | conjIntro _ _ left right => exact ⟨left valid, right valid⟩
  | conjLeft _ ih => exact (ih valid).1
  | conjRight _ ih => exact (ih valid).2
  | negIntro _ _ positive negative =>
    intro hF
    have extended := holdsWith valid hF
    exact negative extended (positive extended)
  | @reductio _ F _ _ _ positive negative =>
    refine Classical.byContradiction fun notF => ?_
    have extended := holdsWith valid (show (Formula.neg F).Holds σ i from notF)
    exact negative extended (positive extended)

theorem stl6 (F G : Formula S) (σ : Behavior S) :
    (conj (eventually (always F)) (eventually (always G))).Sat σ ↔
      (eventually (always (conj F G))).Sat σ := by
  constructor
  · rintro ⟨hF, hG⟩
    obtain ⟨i, _, hF⟩ := (holds_eventually _ σ 0).mp hF
    obtain ⟨j, _, hG⟩ := (holds_eventually _ σ 0).mp hG
    apply (holds_eventually _ σ 0).mpr
    refine ⟨max i j, Nat.zero_le _, fun k hk => ⟨?_, ?_⟩⟩
    · exact hF k (Nat.le_trans (Nat.le_max_left ..) hk)
    · exact hG k (Nat.le_trans (Nat.le_max_right ..) hk)
  · intro h
    obtain ⟨i, hi, h⟩ := (holds_eventually _ σ 0).mp h
    exact ⟨(holds_eventually _ σ 0).mpr ⟨i, hi, fun k hk => (h k hk).1⟩,
      (holds_eventually _ σ 0).mpr ⟨i, hi, fun k hk => (h k hk).2⟩⟩

theorem lattice {smaller : ι → ι → Prop} (order : WellFounded smaller)
    {F G : Formula S} {H : ι → Formula S}
    (step : ∀ c σ, F.Sat σ → ∀ i, (H c).Holds σ i →
      ∃ j, i ≤ j ∧ (G.Holds σ j ∨ ∃ d, smaller d c ∧ (H d).Holds σ j)) :
    ∀ σ, F.Sat σ → ∀ i, (∃ c, (H c).Holds σ i) → ∃ j, i ≤ j ∧ G.Holds σ j := by
  intro σ hF
  -- Keep this behavior and its initial F fixed across all ranks and instants.
  have progress (c : ι) : ∀ i, (H c).Holds σ i → ∃ j, i ≤ j ∧ G.Holds σ j := by
    induction c using order.induction with
    | h c smallerProgress =>
      intro i hc
      obtain ⟨j, hij, hG | ⟨d, hdc, hd⟩⟩ := step c σ hF i hc
      · exact ⟨j, hij, hG⟩
      · obtain ⟨k, hjk, hG⟩ := smallerProgress d hdc j hd
        exact ⟨k, Nat.le_trans hij hjk, hG⟩
  rintro i ⟨c, hc⟩
  exact progress c i hc

end Silmaril.Proofs.Logic.Temporal.TLA.Rules.Figure5
