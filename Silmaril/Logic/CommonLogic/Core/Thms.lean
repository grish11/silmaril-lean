module

public import Silmaril.Logic.CommonLogic.Core.Defs

@[expose] public section

namespace Silmaril.Logic.CommonLogic.Core

open CategoryTheory

def TheoryHolds {S : Signature} (M : Model S) (H : Set (Sentence S)) : Prop :=
  ∀ p ∈ H, (room S).Sat M p

def Sat {S : Signature} (H : Set (Sentence S)) : Prop := ∃ M, TheoryHolds M H

def Unsat {S : Signature} (H : Set (Sentence S)) : Prop := ¬ Sat H

/-- Consequence survives arbitrary sort-class-preserving symbol renaming. -/
theorem entails_map {S T : Signature} (f : S ⟶ T) {H : Set (Sentence S)} {p : Sentence S}
    (h : (room S).Entails H p) :
    (room T).Entails (Formula.map f '' H) (p.map f) :=
  (corridor f).entails_map h

/-- Unlike the public empty-carrier FOL option, every CL discourse has an individual. -/
theorem individual_exists {S : Signature} (M : Model S) :
    (room S).Sat M (.ex (.equal (.var 0) (.var 0))) := by
  obtain ⟨x⟩ := M.nonempty
  exact ⟨x, rfl⟩

/-- Sequence quantification always includes the empty sequence. -/
theorem empty_sequence_exists {S : Signature} (M : Model S) :
    (room S).Sat M (.exSeq .tt) := ⟨[], True.intro⟩

/-- info: 'Silmaril.Logic.CommonLogic.Core.Formula.holds_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Formula.holds_map
/-- info: 'Silmaril.Logic.CommonLogic.Core.entails_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entails_map
/-- info: 'Silmaril.Logic.CommonLogic.Core.individual_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms individual_exists

end Silmaril.Logic.CommonLogic.Core
