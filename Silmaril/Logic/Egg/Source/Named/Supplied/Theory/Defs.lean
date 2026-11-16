module

public import Silmaril.Logic.Egg.Source.Named.Supplied.Institution.Defs
public import Silmaril.Logic.Egg.Source.Named.Theory.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named.Supplied.Direct

/-- Arbitrary complete supplied files share one ambient algebra. -/
def TheoryHolds {S : SuppliedSignature} (M : Core.Model S.ambient)
    (H : Set (Sentence S)) : Prop := ∀ p ∈ H, Holds M p

def flatten {S : SuppliedSignature} (H : Set (Sentence S)) : Set (Core.Rule S.ambient) :=
  {r | ∃ p ∈ H, r ∈ decode p}

theorem theoryHolds_iff {S : SuppliedSignature} (M : Core.Model S.ambient)
    (H : Set (Sentence S)) : TheoryHolds M H ↔ CoreTheoryHolds M (flatten H) := by
  constructor
  · intro h r hr
    obtain ⟨p, hp, member⟩ := hr
    exact (decode_holds M p).mpr (h p hp) r member
  · intro h p hp
    apply (decode_holds M p).mp
    intro r hr
    exact h r ⟨p, hp, hr⟩

def Satisfiable {S : SuppliedSignature} (H : Set (Sentence S)) : Prop :=
  ∃ M : Core.Model S.ambient, TheoryHolds M H

theorem satisfiable_iff {S : SuppliedSignature} (H : Set (Sentence S)) :
    Satisfiable H ↔ CoreSatisfiable (flatten H) :=
  exists_congr (fun M => theoryHolds_iff M H)

theorem unsatisfiable_iff {S : SuppliedSignature} (H : Set (Sentence S)) :
    (¬ Satisfiable H) ↔ ¬ CoreSatisfiable (flatten H) :=
  not_congr (satisfiable_iff H)

def Entails {S : SuppliedSignature} (H : Set (Sentence S)) (p : Sentence S) : Prop :=
  ∀ M : Core.Model S.ambient, TheoryHolds M H → Holds M p

theorem entails_iff {S : SuppliedSignature} (H : Set (Sentence S)) (p : Sentence S) :
    Entails H p ↔ ∀ r ∈ decode p, CoreEntails (flatten H) r := by
  constructor
  · intro h r hr M hM
    exact (decode_holds M p).mpr (h M ((theoryHolds_iff M H).mpr hM)) r hr
  · intro h M hM
    apply (decode_holds M p).mp
    intro r hr
    exact h r hr M ((theoryHolds_iff M H).mp hM)

theorem every_theory_satisfiable {S : SuppliedSignature} (H : Set (Sentence S)) :
    Satisfiable H := by
  refine ⟨singletonModel S.ambient, ?_⟩
  apply (theoryHolds_iff _ H).mpr
  intro r _
  exact singleton_rule S.ambient r

end Silmaril.Logic.Egg.Source.Named.Supplied.Direct
