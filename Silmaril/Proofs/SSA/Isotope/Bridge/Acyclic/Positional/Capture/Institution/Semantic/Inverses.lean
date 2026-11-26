module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Semantic.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room Corridor)
open Silmaril.SSA.LambdaRTL.Quotient

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

theorem ranked_roundTrip_proof (K : (rankedRoom J P).Mod) (e : RankedEquation P) :
    (rankedRoom J P).Sat K (numberGrammar (readGrammar e)) ↔ (rankedRoom J P).Sat K e := by
  change denoteRanked J K.fromShrinkHoms.as (ofGrammar e.2.1.toGrammar) =
    denoteRanked J K.fromShrinkHoms.as (ofGrammar e.2.2.toGrammar) ↔ _
  rw [denoteRanked_roundTrip, denoteRanked_roundTrip]
  rfl

omit [FreydCategory.CentralUnit J] in
theorem grammar_roundTrip_proof (A : (grammarRoom J P).Mod) (e : GrammarEquation P) :
    (grammarRoom J P).Sat A (readGrammar (numberGrammar e)) ↔ (grammarRoom J P).Sat A e :=
  Iff.of_eq (congrArg ((validatedRoom J P).Sat A) (grammarCase_roundTrip e))

set_option backward.isDefEq.respectTransparency false in
theorem read_number_quot_proof (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) :
    Corridor.quot (readCorridor J P) ≫ Corridor.quot (numberCorridor J P) =
      𝟙 (Silmaril.SSA.LambdaRTL.Quotient.Room.quot (rankedRoom J P)) := by
  apply Room.hom_ext
  · funext q
    induction q using Quotient.ind with
    | _ e => exact Quotient.sound (fun K => ranked_roundTrip_proof K e)
  · exact (validatedModelIso (J := J) P).counit_eq

set_option backward.isDefEq.respectTransparency false in
theorem number_read_quot_proof (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) :
    Corridor.quot (numberCorridor J P) ≫ Corridor.quot (readCorridor J P) =
      𝟙 (Silmaril.SSA.LambdaRTL.Quotient.Room.quot (grammarRoom J P)) := by
  apply Room.hom_ext
  · funext q
    induction q using Quotient.ind with
    | _ e => exact Quotient.sound (fun A => grammar_roundTrip_proof A e)
  · exact (validatedModelIso (J := J) P).unit_eq.symm

end Silmaril.Isotope.Institution.Acyclic.Captured
