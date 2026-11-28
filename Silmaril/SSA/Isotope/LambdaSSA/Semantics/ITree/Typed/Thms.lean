module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedSingleton

/-! # Typing coherence and singleton evaluation in the ITree Kleisli model -/

public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed

open CategoryTheory
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

variable {κ : Type (v + 1)} [AtomValues κ] {E : Type v → Type v}
  {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]

attribute [local instance] typeModel categoricalInstructions

variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]
  (raw : Primitive E Φ (Sigma (AtomValues.carrier (κ := κ))))

local notation "V" => AtomValues.carrier (κ := κ)
local notation "TM" => ModelTree E
local notation "J" => typeJ (m := TM)
local notation "T" => Categorical.ofMonadicTypeModel (τ := Ty κ)

/-- At fixed exact input and exit types, the structural categorical witnesses
agree. The proof compares their images under the injective typed exit encoding. -/
theorem regionTypingCoherent
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := TM) f x⟩ raw) :
    Categorical.RegionTypingCoherent (Φ := Φ) J T :=
  Erasure.regionTypingCoherent (m := TM) raw Elgot.ITree.diverge Elgot.ITree.diverge compat

/-- The ordinary singleton Kleisli denotation computes the erased ITree on
encoded inputs and encodes its output at label zero. -/
theorem singletonDenote_tree
    (compat : Compatible (κ' := κ) ⟨fun f x =>
      InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := TM) f x⟩ raw)
    {A B : Ty κ} {r : Region Φ} (hr : Region.HasType [A] r [B])
    (a : Ty.denote V A) (env : Env (Sigma V)) :
    ((show TM _ from (Categorical.denoteSingletonRegion J T hr).of a) >>=
      fun b => pure (0, encodeValue V B b)) =
        region raw (extend env (encodeValue V A a)) r :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.singletonDenote_tree raw compat hr a env

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
