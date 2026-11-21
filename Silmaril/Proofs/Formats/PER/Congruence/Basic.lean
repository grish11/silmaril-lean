module
public import Silmaril.Formats.PER.Congruence.Defs

public section
namespace Silmaril.Proofs.Formats.PER.Congruence
open Silmaril.Formats Silmaril.Formats.PER
variable {α : Type}

theorem sInf_isGLB (family : Set (PER α)) :
    IsGLB family (PER.iInf fun member : family => member.val) := by
  constructor
  · intro R member left right h
    exact h ⟨R, member⟩
  · intro R lower left right h member
    exact lower member.property h

theorem generated_closed (C : Constructors α) (R : PER α) : C.Closed (C.generated R) := by
  intro shape left right hl hr h target
  exact target.property.2 shape hl hr (fun pos => h pos target)

theorem map_generated {β : Type} (C : Constructors α) (D : Constructors β)
    (f : α → β) {R : PER α} {S : PER β} (seed : R ≤ S.pull f)
    (closed : C.Closed ((D.generated S).pull f)) :
    C.generated R ≤ (D.generated S).pull f := by
  have lower : R ≤ (D.generated S).pull f := fun _ _ h target => target.property.1 (seed h)
  exact fun _ _ h => h ⟨_, lower, closed⟩

end Silmaril.Proofs.Formats.PER.Congruence
