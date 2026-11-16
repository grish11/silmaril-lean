module

public import Silmaril.Logic.Kore.Operational.Conditional.RuleSystem.Defs

@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.RuleSystem

theorem wellDefined (rules : List Rule) :
    Reachability.RuleSystem.WeaklyWellDefined (schemes rules) := by
  intro r v c hc
  exact ⟨r.val.afterConfig v, rfl⟩

theorem induced_iff (rules : List Rule) (c d : Config) :
    Reachability.RuleSystem.Induced (schemes rules) c d ↔ Step rules c d := by
  rw [step_iff]
  constructor
  · rintro ⟨⟨r, hr⟩, v, ⟨hc, hg, he⟩, hd⟩
    exact ⟨r, hr, v, hc, hg, he, hd⟩
  · rintro ⟨r, hr, v, hc, hg, he, hd⟩
    exact ⟨⟨r, hr⟩, v, ⟨hc, hg, he⟩, hd⟩

/-- General certificates permit overlapping competitors and multi-step targets.
The captured claim valuation is independent of the operational rule valuations. -/
theorem allPartial_of_certificate (rules : List Rule) (Q : Config → Prop) (n : Nat)
    (cert : Reachability.RuleSystem.Certificate (schemes rules) Q n)
    (c : Config) (entry : Q c ∨ ∃ j, cert.node j c) :
    Reachability.AllPartial (Step rules) Q c := by
  have relation : Step rules = Reachability.RuleSystem.Induced (schemes rules) := by
    funext c d
    exact propext (induced_iff rules c d).symm
  rw [relation]
  exact cert.sound (wellDefined rules) entry

end Silmaril.Logic.Kore.Operational.Conditional.RuleSystem
