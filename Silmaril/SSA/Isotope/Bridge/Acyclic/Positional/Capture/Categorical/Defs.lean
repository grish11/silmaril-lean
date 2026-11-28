module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.Thms

/-! # Native contextual dispatcher for a captured positional table -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel routeEnvironment retainEnvironment)
open LetIter.ProofRelevant.Semantics.Categorical (contextualLoop caseWithContext)
open Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical (localInject)

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

local notation "E" => ctxObj M β.toList

/-- Pure projection to the shared ambient variables. -/
def Scope.projection : {m : Nat} → {γ : BoundCtx τ m} → Scope β γ →
    (ctxObj M γ.toList ⟶ E)
  | _, _, .base => 𝟙 _
  | _, _, .skip s A => fst _ (M.obj A) ≫ s.projection

/-- The exact operand as an expression of the native positional language. -/
noncomputable def denoteOperand {m : Nat} {γ : BoundCtx τ m} {A : τ} (a : Operand Φ γ A) :
    J.obj (ctxObj M γ.toList) ⟶ J.obj (M.obj A) :=
  denote J M (Morphism.CaseSSA.erase_hasType a.2.toHasType)

noncomputable def Table.blockArrow (p : Table Φ β L n) (i : Fin (n + 1)) :
    J.obj (E ⊗ M.obj (p.types i)) ⟶ J.obj (labelObj M (List.ofFn p.types ++ L)) :=
  denoteRegion J M (p.block i).toSSA_hasType

noncomputable def Table.collective (p : Table Φ β L n) :
    J.obj (E ⊗ finiteLabelObj M p.types) ⟶ J.obj (labelObj M (List.ofFn p.types ++ L)) :=
  (collectiveDenotes_exists_succ J M n β.toList p.types L (p.blockArrow J M)).choose

theorem Table.collective_spec (p : Table Φ β L n) :
    CollectiveDenotes J M β.toList p.types L (p.blockArrow J M) (p.collective J M) :=
  (collectiveDenotes_exists_succ J M n β.toList p.types L (p.blockArrow J M)).choose_spec

/-- One native dispatcher step from the coproduct of local packet types. -/
noncomputable def Table.dispatch (p : Table Φ β L n) :
    J.obj (E ⊗ labelObj M (List.ofFn p.types)) ⟶ J.obj (labelObj M (List.ofFn p.types ++ L)) :=
  J.map (E ◁ labelObjToFinite M p.types) ≫ p.collective J M

noncomputable def Table.loop (p : Table Φ β L n) :
    J.obj (E ⊗ labelObj M (List.ofFn p.types)) ⟶ J.obj (labelObj M L) :=
  contextualLoop J (p.dispatch J M ≫ J.map (labelAppendSplit M (List.ofFn p.types) L))

/-- Enter the original dispatcher with the shared values and the selected packet. -/
noncomputable def Table.resultAt (p : Table Φ β L n) (i : Fin (n + 1)) :
    J.obj (E ⊗ M.obj (p.types i)) ⟶ J.obj (labelObj M L) :=
  J.map (E ◁ localInject M p.types i) ≫ p.loop J M

noncomputable def Table.boundary (p : Table Φ β L n) :
    J.obj (E ⊗ labelObj M (List.ofFn p.types ++ L)) ⟶ J.obj (labelObj M L) :=
  J.map (E ◁ labelAppendSplit M (List.ofFn p.types) L) ≫
    routeEnvironment J E (labelObj M L) (labelObj M (List.ofFn p.types)) ≫
      coprod.desc (J.map (snd E _)) (p.loop J M)

/-- Native continuation of a target with the original shared context retained. -/
noncomputable def Target.route (p : Table Φ β L n) {A : τ} : Target p.types L A →
    (J.obj (E ⊗ M.obj A) ⟶ J.obj (labelObj M L))
  | .local i => p.resultAt J M i
  | .exit (i := i) h => J.map (snd E (M.obj A) ≫ labelInject M i h)

/-- Run a block with its original captured values and dispatch on its result.
The old packet is available to the operand and dropped before the next block. -/
noncomputable def Block.continued (p : Table Φ β L n) {A : τ} :
    Block Φ β p.types L A → (J.obj (E ⊗ M.obj A) ⟶ J.obj (labelObj M L))
  | .jump a t => retainEnvironment J (fst E (M.obj A)) (denoteOperand J M a) ≫ t.route J M p
  | .case (B := B) (D := D) a l r =>
    caseWithContext J (denoteOperand J M a ≫ J.map (M.coprodIso B D).hom)
      (J.map (fst E (M.obj A) ▷ M.obj B) ≫ l.route J M p)
      (J.map (fst E (M.obj A) ▷ M.obj D) ≫ r.route J M p)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
