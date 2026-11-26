module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.TypedCoherence

/-! # Exact region coherence from erased execution -/

public section

universe v q

namespace Silmaril.Isotope.LambdaSSA.Semantics.Erasure

open Silmaril.Elgot
open Interaction (Transfer)
open Interaction.Typed (AtomValues typeModel)
open Isotope.Semantics (encodeValue)
open LetIter.ProofRelevant.Semantics (InstructionModel)
open LetIter.ProofRelevant.Semantics.Categorical (typeJ)

variable {κ : Type v} [AtomValues κ] {Φ : Type q} [HasTy Φ (Ty κ)] [HasEff Φ Bool]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

attribute [local instance] typeModel

local notation "V" => AtomValues.carrier (κ := κ)

variable [InstructionModel Φ (Ty κ) Bool m]

/-- Every exact structural region witness agrees after erasing intermediate
types, including the arbitrary internal label types of cyclic dispatchers.
Injectivity at the fixed outward interface gives equality of the arrows. -/
theorem regionTypingCoherent
    (raw : Primitive m Φ (Sigma V)) (badTerm : m (Value (Sigma V))) (badRegion : m (Transfer (Sigma V)))
    (compat : ∀ f (x : Ty.denote V (instrSrc f)), raw f (encodeValue V _ x) =
      (InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := m) f x >>= fun y => pure (encodeValue V _ y))) :
    letI := Categorical.ofMonadicInstructionModel (τ := Ty κ) (Φ := Φ) (ε := Bool) (m := m)
    Categorical.RegionTypingCoherent (Φ := Φ) (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := Ty κ)) :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.coherence_of_erasure raw badTerm badRegion compat

end Silmaril.Isotope.LambdaSSA.Semantics.Erasure
