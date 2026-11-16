module

public import Silmaril.Logic.Temporal.LTL.NNF.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.LTL.NNF.Recurrence

/-- Strong until: a finite right-hand witness, with left truth strictly before it. -/
def strongUntil (P Q : Nat → Prop) (n : Nat) : Prop :=
  ∃ d, Q (n+d) ∧ ∀ i, i < d → P (n+i)

/-- Release includes the current right-hand requirement. A left witness only
releases requirements at strictly later positions; endless right truth suffices. -/
def release (P Q : Nat → Prop) (n : Nat) : Prop :=
  ∀ d, Q (n+d) ∨ ∃ i, i < d ∧ P (n+i)

theorem holds_until {Atom : Type} (word : Nat → Atom → Prop)
    (p q : Formula Atom) (n : Nat) :
    (Formula.until p q).Holds word n ↔ strongUntil (p.Holds word) (q.Holds word) n :=
  Iff.rfl

theorem holds_release {Atom : Type} (word : Nat → Atom → Prop)
    (p q : Formula Atom) (n : Nat) :
    (Formula.release p q).Holds word n ↔ release (p.Holds word) (q.Holds word) n :=
  Iff.rfl

end Silmaril.Logic.Temporal.LTL.NNF.Recurrence
