module

public import Silmaril.Logic.Reachability.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability

/-- Finite reachability is precisely a finite transition closure ending in the target. -/
theorem reaches_iff_reflTransGen {W : Type} {R : W → W → Prop} {Q : W → Prop} {w : W} :
    Reaches R Q w ↔ ∃ v, Relation.ReflTransGen R w v ∧ Q v := by
  constructor
  · intro h
    induction h with
    | now hq => exact ⟨_, .refl, hq⟩
    | next _ hstep _ ih =>
      obtain ⟨v, hpath, hq⟩ := ih
      exact ⟨v, hpath.head hstep, hq⟩
  · rintro ⟨v, hpath, hq⟩
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => exact .now hq
    | head hstep _ ih => exact .next trivial hstep ih

end Silmaril.Logic.Reachability
