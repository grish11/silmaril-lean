module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Dispatcher
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Compile

/-! # Native denotation of the captured positional lowering -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

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

variable [RegionTypingCoherent (Φ := Φ) J M]

/-- Evaluate the original entry operand and carry its ambient context into the
unchanged native contextual dispatcher. -/
theorem Table.toSSA_denote (p : Table Φ β L n) (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) =
      LetIter.ProofRelevant.Semantics.Categorical.bind J (denoteOperand J M a) (p.resultAt J M i) :=
  toSSA_denote_proof J M p i a

variable [FreydCategory.CentralUnit J]

/-- One step retains the ambient variables and executes only the selected
continuation. The block computation runs before its target. -/
theorem Table.resultAt_step (p : Table Φ β L n) (i : Fin (n + 1)) :
    p.resultAt J M i = (p.block i).continued J M p :=
  resultAt_step_proof J M p i

/-- Introduced binders change the pure projection to the ambient variables. -/
theorem Table.compileAt_denote (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) :
    denoteRegion J M (p.compileAt ok i s).toSSA_hasType =
      J.map (s.projection M ▷ M.obj (p.types i)) ≫ p.resultAt J M i :=
  compileAt_denote_proof J M p ok i s

/-- The structured lowering preserves the exact native arrow at the original
ordered exits, with no commutativity requirement on primitive arrows. -/
theorem Table.toFiniteExit_denote (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toFiniteExit ok i a).toSSA_hasType = denoteRegion J M (p.toSSA_hasType i a) :=
  toFiniteExit_denote_proof J M p ok i a

/-- The decoded LetCase term has the native region's arrow in the same model. -/
theorem Table.toLetCase_denote (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M (p.toLetCase ok i a).2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) :=
  toLetCase_denote_proof J M p ok i a

/-- Every successful checked compilation satisfies the same ordered-exit square. -/
theorem Table.toLetCase?_denote (p : Table Φ β L n) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) {term : Operand Φ β (Region.packedExitType L)}
    (compiled : p.toLetCase? i a = some term) :
    denoteRegion J M (p.toSSA_hasType i a) =
      J.map (contextMap M β) ≫ LetCase.Semantics.Categorical.denote J M term.2 ≫
        J.map (labelInject M (L := [Region.packedExitType L]) 0 rfl ≫ unpackLabelExit M L) :=
  toLetCase?_denote_proof J M p i a compiled

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
