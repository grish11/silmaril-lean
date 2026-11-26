module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Categorical.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional

/-! # Agreement of ranked positional SSA, structured SSA, and exact LetCase -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open Silmaril.SSA.RVSDG.LambdaSSA
open LambdaSSA.Semantics.Categorical
  (RegionTypingCoherent denoteRegion denote ctxObj labelInject unpackLabelExit)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w h k

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {n : Nat} {L : LCtx τ}

/-- One step runs the current primitive before transferring its result. A case
uses the coproduct to select precisely one of the two continuations. -/
theorem Table.resultAt_step (p : Table Φ L n) (i : Fin n) :
    p.resultAt J M i =
      Acyclic.Categorical.blockArrow J M (fun _ s => (p.destination s).result J M) (p.block i) :=
  resultAt_step_proof J M p i

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

/-- The finite unfolding computes the native dispatcher on a block payload,
in any surrounding context. -/
theorem Table.compileRankedAt_denote (p : Table Φ L n) (ranking : Ranking p) (i : Fin n)
    {d : Nat} (β : BoundCtx τ d) :
    denoteRegion J M (p.compileRankedAt ranking i β).toSSA_hasType =
      J.map (snd (ctxObj M β.toList) (M.obj (p.types i))) ≫ p.resultAt J M i :=
  compileRankedAt_denote_proof J M p ranking i β

theorem Table.compileAt_denote (p : Table Φ L n) (ok : p.Forward) (i : Fin n)
    {d : Nat} (β : BoundCtx τ d) :
    denoteRegion J M (p.compileAt ok i β).toSSA_hasType =
      J.map (snd (ctxObj M β.toList) (M.obj (p.types i))) ≫ p.resultAt J M i :=
  p.compileRankedAt_denote J M (p.forwardRanking ok) i β

/-- Evaluate the operand once, then enter the native dispatcher with the
resulting payload. This equation also holds before the forward-edge check. -/
theorem Table.toSSA_denote (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d}
    (i : Fin n) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) =
      denote J M (Morphism.CaseSSA.erase_hasType a.2.toHasType) ≫ p.resultAt J M i :=
  toSSA_denote_proof J M p i a

/-- The source positional CFG and the structured lowering have identical
native computation arrows at the original ordered exit interface. -/
theorem Table.toFiniteExitRanked_denote (p : Table Φ L n) (ranking : Ranking p)
    {d : Nat} {β : BoundCtx τ d} (i : Fin n) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toFiniteExitRanked ranking i a).toSSA_hasType =
      denoteRegion J M (p.toSSA_hasType i a) :=
  toFiniteExitRanked_denote_proof J M p ranking i a

theorem Table.toFiniteExit_denote (p : Table Φ L n) (ok : p.Forward)
    {d : Nat} {β : BoundCtx τ d} (i : Fin n) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toFiniteExit ok i a).toSSA_hasType =
      denoteRegion J M (p.toSSA_hasType i a) :=
  p.toFiniteExitRanked_denote J M (p.forwardRanking ok) i a

/-- Exact LetCase computes the same arrow after the input environment
comparison and the native decoder for the ordered exit list. -/
theorem Table.toLetCaseRanked_denote (p : Table Φ L n) (ranking : Ranking p)
    {d : Nat} {β : BoundCtx τ d} (i : Fin n) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫
        LetCase.Semantics.Categorical.denote J M (p.toLetCaseRanked ranking i a).2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) :=
  toLetCaseRanked_denote_proof J M p ranking i a

/-- Every successful checked translation agrees with the unchanged native table. -/
theorem Table.toLetCase?_denote (p : Table Φ L n) {d : Nat} {β : BoundCtx τ d}
    (i : Fin n) (a : Operand Φ β (p.types i)) {term : Operand Φ β (Region.packedExitType L)}
    (compiled : p.toLetCase? i a = some term) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M term.2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) :=
  toLetCase?_denote_proof J M p i a compiled

theorem Table.toLetCase_denote (p : Table Φ L n) (ok : p.Forward)
    {d : Nat} {β : BoundCtx τ d} (i : Fin n) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫
        LetCase.Semantics.Categorical.denote J M (p.toLetCase ok i a).2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) :=
  p.toLetCaseRanked_denote J M (p.forwardRanking ok) i a

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional
