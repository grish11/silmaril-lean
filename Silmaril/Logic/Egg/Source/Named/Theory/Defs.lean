module

public import Silmaril.Logic.Egg.Source.Named.Family.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open Silmaril.Logic.Institution.Examples

/-- Union of all decoded rules from all original files. This is a theory over
one fixed ambient signature, not a family of unrelated per-file models. -/
def flatten {S : Core.Signature} (H : Set (FamilySentence S)) : Set (Core.Rule S) :=
  {r | ∃ p ∈ H, r ∈ p.decode}

def TheoryHolds {S : Core.Signature} (M : Core.Model S)
    (H : Set (FamilySentence S)) : Prop := ∀ p ∈ H, p.Holds M

def CoreTheoryHolds {S : Core.Signature} (M : Core.Model S)
    (H : Set (Core.Rule S)) : Prop := ∀ r ∈ H, r.Holds M

theorem theoryHolds_iff {S : Core.Signature} (M : Core.Model S)
    (H : Set (FamilySentence S)) : TheoryHolds M H ↔ CoreTheoryHolds M (flatten H) := by
  constructor
  · intro h r hr
    obtain ⟨p, hp, member⟩ := hr
    exact (p.decode_holds M).mpr (h p hp) r member
  · intro h p hp
    apply (p.decode_holds M).mp
    intro r hr
    exact h r ⟨p, hp, hr⟩

def Satisfiable {S : Core.Signature} (H : Set (FamilySentence S)) : Prop :=
  ∃ M : Core.Model S, TheoryHolds M H

def CoreSatisfiable {S : Core.Signature} (H : Set (Core.Rule S)) : Prop :=
  ∃ M : Core.Model S, CoreTheoryHolds M H

theorem satisfiable_iff {S : Core.Signature} (H : Set (FamilySentence S)) :
    Satisfiable H ↔ CoreSatisfiable (flatten H) :=
  exists_congr (fun M => theoryHolds_iff M H)

theorem unsatisfiable_iff {S : Core.Signature} (H : Set (FamilySentence S)) :
    (¬ Satisfiable H) ↔ ¬ CoreSatisfiable (flatten H) :=
  not_congr (satisfiable_iff H)

def Entails {S : Core.Signature} (H : Set (FamilySentence S)) (p : FamilySentence S) : Prop :=
  ∀ M : Core.Model S, TheoryHolds M H → p.Holds M

def CoreEntails {S : Core.Signature} (H : Set (Core.Rule S)) (r : Core.Rule S) : Prop :=
  ∀ M : Core.Model S, CoreTheoryHolds M H → r.Holds M

theorem entails_iff {S : Core.Signature} (H : Set (FamilySentence S)) (p : FamilySentence S) :
    Entails H p ↔ ∀ r ∈ p.decode, CoreEntails (flatten H) r := by
  constructor
  · intro h r hr M hM
    exact (p.decode_holds M).mpr (h M ((theoryHolds_iff M H).mpr hM)) r hr
  · intro h M hM
    apply (p.decode_holds M).mp
    intro r hr
    exact h r hr M ((theoryHolds_iff M H).mp hM)

/-- Pure conditional-equational logic has a singleton model at every sort.
There are no hidden denials or disequalities in this source language. -/
def singletonModel (S : Core.Signature) : Core.Model S where
  carrier := fun _ => Unit
  op := fun _ _ => ()

theorem singleton_rule (S : Core.Signature) (r : Core.Rule S) :
    r.Holds (singletonModel S) := by
  intro ρ _
  change (_ : Unit) = _
  exact Subsingleton.elim _ _

theorem every_theory_satisfiable {S : Core.Signature} (H : Set (FamilySentence S)) :
    Satisfiable H := by
  refine ⟨singletonModel S, ?_⟩
  apply (theoryHolds_iff _ H).mpr
  intro r _
  exact singleton_rule S r

/-- UNSAT transfer is exact but has no inconsistent example in positive Core. -/
theorem no_unsatisfiable_theory {S : Core.Signature} (H : Set (FamilySentence S)) :
    ¬ (¬ Satisfiable H) := fun h => h (every_theory_satisfiable H)

end Silmaril.Logic.Egg.Source.Named
