module

public import Silmaril.Logic.Prolog.Definite.Defs
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section

namespace Silmaril.Logic.Prolog.Definite

open Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Translation forgets no model data: its model functor is the identity. -/
theorem toFirstOrder_modelExpansive : toFirstOrder.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

def TheoryHolds {S : Signature} (M : Model S) (H : Set (Sentence S)) : Prop :=
  ∀ s ∈ H, s.Holds M

def Sat {S : Signature} (H : Set (Sentence S)) : Prop := ∃ M, TheoryHolds M H

def Unsat {S : Signature} (H : Set (Sentence S)) : Prop := ¬ Sat H

theorem theory_holds_iff_firstOrder {S : Signature} (M : Model S) (H : Set (Sentence S)) :
    TheoryHolds M H ↔ ∀ φ ∈ Sentence.encode '' H, φ.Holds M := by
  constructor
  · rintro h φ ⟨s, hs, rfl⟩
    exact (s.encode_holds M).mpr (h s hs)
  · intro h s hs
    exact (s.encode_holds M).mp (h _ ⟨s, hs, rfl⟩)

theorem sat_iff_firstOrder {S : Signature} (H : Set (Sentence S)) :
    Sat H ↔ ∃ M : FOL.Structure S, ∀ φ ∈ Sentence.encode '' H, φ.Holds M :=
  exists_congr fun M => theory_holds_iff_firstOrder M H

theorem unsat_iff_firstOrder {S : Signature} (H : Set (Sentence S)) :
    Unsat H ↔ ¬ ∃ M : FOL.Structure S, ∀ φ ∈ Sentence.encode '' H, φ.Holds M :=
  not_congr (sat_iff_firstOrder H)

/-- Exact consequence borrowing, with actual source model coverage. -/
theorem entails_iff_firstOrder (S : Signature) (H : Set (Sentence S)) (s : Sentence S) :
    (room S).Entails H s ↔ (FOL.room S).Entails (Sentence.encode '' H) s.encode :=
  toFirstOrder.entails_iff toFirstOrder_modelExpansive S H s

/-- Every sort can be inhabited and every predicate made true. -/
def totalModel (S : Signature) : Model S where
  carrier _ := Unit
  op _ _ := ()
  rel _ _ := True

theorem totalModel_holds {S : Signature} (s : Sentence S) : s.Holds (totalModel S) := by
  cases s with
  | clause c => exact fun _ _ => True.intro
  | query q => exact ⟨fun _ => (), fun _ _ => True.intro⟩

/-- Positive definite theories, even with positive queries, are satisfiable.
UNSAT transport is exact but creates no contradiction in this positive fragment. -/
theorem sat_every_theory {S : Signature} (H : Set (Sentence S)) : Sat H :=
  ⟨totalModel S, fun s _ => totalModel_holds s⟩

theorem not_unsat {S : Signature} (H : Set (Sentence S)) : ¬ Unsat H :=
  fun h => h (sat_every_theory H)

/-- info: 'Silmaril.Logic.Prolog.Definite.entails_iff_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entails_iff_firstOrder
/-- info: 'Silmaril.Logic.Prolog.Definite.sat_iff_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sat_iff_firstOrder
/-- info: 'Silmaril.Logic.Prolog.Definite.unsat_iff_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unsat_iff_firstOrder
/-- info: 'Silmaril.Logic.Prolog.Definite.toFirstOrder_modelExpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toFirstOrder_modelExpansive

end Silmaril.Logic.Prolog.Definite
