module

public import Silmaril.Proofs.Logic.Temporal.Buchi.FixedPoint

@[expose] public section
namespace Silmaril.Logic.Temporal.Buchi

/-- Deadlocks cannot satisfy Büchi acceptance, even if accepting. -/
theorem not_accepts_of_deadlock {W : Type} (R : W → W → Prop) (F : Set W) (w : W)
    (dead : ∀ v, ¬ R w v) : ¬ Accepts R F w := by
  rintro ⟨p, h0, edges, _⟩
  exact dead (p 1) (h0 ▸ edges 0)

/-- Enlarging the transition relation and accepting set preserves a path witness. -/
theorem accepts_mono {W : Type} {R R' : W → W → Prop} {F F' : Set W}
    (hr : ∀ w v, R w v → R' w v) (hf : F ⊆ F') {w : W}
    (h : Accepts R F w) : Accepts R' F' w := by
  obtain ⟨p, h0, edges, visits⟩ := h
  refine ⟨p, h0, fun n => hr _ _ (edges n), ?_⟩
  intro n
  obtain ⟨m, hm, hfm⟩ := visits n
  exact ⟨m, hm, hf hfm⟩

end Silmaril.Logic.Temporal.Buchi
