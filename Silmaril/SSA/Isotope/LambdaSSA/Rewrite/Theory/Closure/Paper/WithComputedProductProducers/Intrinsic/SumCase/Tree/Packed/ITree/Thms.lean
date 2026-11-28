module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms

/-! # Erased execution of the packed case tree -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics
open Semantics.Categorical Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open CategoryTheory

universe v q

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel categoricalInstructions

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]

local notation "V" => AtomValues.carrier (κ := κ)
local notation "J" => typeJ (m := ModelTree E)
local notation "M" => ofMonadicTypeModel (τ := Ty κ)

/-- The selected fold, followed by packing and output encoding, executes
as the actual erased packed region on the encoded input. -/
theorem CaseTree.packedExecution (raw : Primitive E Φ (Sigma V))
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩ raw)
    {X : Ty κ} {L : LCtx (Ty κ)} (p : CaseTree Φ X L) (input : Ty.denote V X) (env : Env (Sigma V)) :
    ((show ModelTree E _ from (p.targetArrow J M ≫ (J).map (packLabel M L)).of input) >>=
      fun b => pure (0, encodeValue V (packedExitType L) b)) =
      region raw (Semantics.extend env (encodeValue V X input)) (packExits p.elaborate.val) := by
  let := regionTypingCoherent raw compat
  rw [← p.denote_packedElaboration J M (fun _ _ => ⟨rfl, rfl⟩)]
  exact singletonDenote_tree raw compat p.elaborate.property.packExits.hasType input env

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic
