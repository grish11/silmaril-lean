module

public import Silmaril.Logic.Prolog.Horn.Defs
public import Silmaril.Logic.Institution.Borrowing

@[expose] public section

namespace Silmaril.Logic.Prolog.Horn

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


end Silmaril.Logic.Prolog.Horn
