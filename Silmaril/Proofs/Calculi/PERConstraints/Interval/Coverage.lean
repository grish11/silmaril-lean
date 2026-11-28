module

public import Silmaril.Calculi.PERConstraints.Interval.Defs

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.IntervalProofs

open Silmaril.Formats

variable {α β : Type}

/-- Glue the source PER to the target lower bound. A new edge consists of a
source edge with either endpoint moved along a lower-bound edge. -/
theorem pull_surjOn_of_injective (bounds : Bounds β) {rename : α → β}
    (injective : Function.Injective rename) :
    Set.SurjOn (fun model => model.pull rename) (bounds.completions (fun _ => True))
      ((bounds.pull rename).completions (fun _ => True)) := by
  intro source hs
  let reach (x y : β) := x = y ∨ bounds.lower.rel x y
  have refl (x : β) : reach x x := Or.inl rfl
  have symm {x y : β} : reach x y → reach y x :=
    fun h => h.elim (fun same => Or.inl same.symm) (fun edge => Or.inr (bounds.lower.laws.symm edge))
  have trans {x y z : β} (h : reach x y) (k : reach y z) : reach x z := by
    rcases h with same | edge
    · exact same ▸ k
    rcases k with same | next
    · exact same ▸ Or.inr edge
    exact Or.inr (bounds.lower.laws.trans edge next)
  have move {x a b y : β} (h : reach x a) (edge : bounds.upper.rel a b) (k : reach b y) :
      bounds.upper.rel x y := by
    have fromLeft : bounds.upper.rel x b := h.elim (· ▸ edge)
      (fun link => bounds.upper.laws.trans (bounds.ordered link) edge)
    exact k.elim (fun same => same ▸ fromLeft)
      (fun link => bounds.upper.laws.trans fromLeft (bounds.ordered link))
  have bridge {a b c d : α} (h : source.rel a b) (link : reach (rename b) (rename c))
      (k : source.rel c d) : source.rel a d := by
    rcases link with same | edge
    · exact source.laws.trans h (injective same ▸ k)
    exact source.laws.trans (source.laws.trans h (hs.1.1 edge)) k
  let glued (x y : β) := bounds.lower.rel x y ∨
    ∃ a b, reach x (rename a) ∧ source.rel a b ∧ reach (rename b) y
  have symmGlued {x y : β} : glued x y → glued y x := by
    rintro (edge | ⟨a, b, ha, edge, hb⟩)
    · exact Or.inl (bounds.lower.laws.symm edge)
    exact Or.inr ⟨b, a, symm hb, source.laws.symm edge, symm ha⟩
  have transGlued {x y z : β} : glued x y → glued y z → glued x z := by
    rintro (h | ⟨a, b, ha, h, hb⟩) (k | ⟨c, d, hc, k, hd⟩)
    · exact Or.inl (bounds.lower.laws.trans h k)
    · exact Or.inr ⟨c, d, trans (Or.inr h) hc, k, hd⟩
    · exact Or.inr ⟨a, b, ha, h, trans hb (Or.inr k)⟩
    · exact Or.inr ⟨a, d, ha, bridge h (trans hb hc) k, hd⟩
  let model : PER β := ⟨glued, ⟨fun _ _ => symmGlued, fun _ _ _ => transGlued⟩⟩
  refine ⟨model, ⟨⟨fun _ _ h => Or.inl h, ?_⟩, trivial⟩, ?_⟩
  · rintro x y (edge | ⟨a, b, ha, edge, hb⟩)
    · exact bounds.ordered edge
    exact move ha (hs.1.2 edge) hb
  · apply PER.ext
    intro x y
    constructor
    · rintro (edge | ⟨a, b, ha, edge, hb⟩)
      · exact hs.1.1 edge
      have left : source.rel x b := ha.elim (fun same => injective same ▸ edge)
        (fun link => source.laws.trans (hs.1.1 link) edge)
      exact hb.elim (fun same => injective same ▸ left)
        (fun link => source.laws.trans left (hs.1.1 link))
    · intro edge
      exact Or.inr ⟨x, y, refl _, edge, refl _⟩

end Silmaril.Calculi.PERConstraints.IntervalProofs
