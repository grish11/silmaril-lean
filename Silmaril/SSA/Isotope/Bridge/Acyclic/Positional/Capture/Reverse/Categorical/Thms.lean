module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Thms

/-! # Ordered-exit round trip for the captured LetCase grammar -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v x y h k

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type x} {C : Type y} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {d : Nat} {β : BoundCtx τ d} {L : LCtx τ} {n : Nat}

variable [RegionTypingCoherent (Φ := Φ) J M] [FreydCategory.CentralUnit J]

/-- Reification realizes the exact LetCase term at the original ordered exits.
The ambient context and the primitive interpretation are shared. -/
theorem ResultGrammar.denote_toTable {term : Operand Φ β (Region.packedExitType L)}
    (g : ResultGrammar term) :
    denoteRegion J M g.toTable.toSSA_hasType =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M term.2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) :=
  (g.toTable.table.toLetCase_denote J M g.toTable.checked 0 g.toTable.entry).trans
    (congrArg (fun t : Operand Φ β (Region.packedExitType L) =>
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M t.2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L))
      g.toTable_toLetCase)

/-- Round trip after an actual successful forward compilation. Any grammar
witness of that exact output can be used for the reverse step. -/
theorem ResultGrammar.denote_roundTrip {term : Operand Φ β (Region.packedExitType L)}
    (g : ResultGrammar term) (p : Table Φ β L n) (i : Fin (n + 1)) (a : Operand Φ β (p.types i))
    (result : p.toLetCase? i a = some term) :
    denoteRegion J M g.toTable.toSSA_hasType = denoteRegion J M (p.toSSA_hasType i a) :=
  (g.denote_toTable J M).trans (p.toLetCase?_denote J M i a result).symm

/-- The witness reconstructed by the forward grammar reader gives a native-arrow
round trip for every checked captured table. -/
theorem denote_tableGrammar_roundTrip (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) :
    denoteRegion J M (tableGrammar p ok i a).toTable.toSSA_hasType =
      denoteRegion J M (p.toSSA_hasType i a) :=
  ((tableGrammar p ok i a).denote_toTable J M).trans (p.toLetCase_denote J M ok i a).symm

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
