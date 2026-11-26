module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Native.Defs
public import Silmaril.SSA.Isotope.LetIter.Thms

/-! # Canonical Kleisli specialization -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory Silmaril.Elgot
open LetIter.ProofRelevant.Semantics (TypeModel InstructionModel)

universe u v w q

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]

/-- Use the value model induced by the same type and coercion interpretations as
proof-relevant LetIter. -/
@[reducible] noncomputable def kleisliTypeModel (τ : Type u) [TypeFormers τ] [Subtyping τ]
    [TypeModel.{u, v} τ] : LetIter.Semantics.Categorical.TypeModel τ (Type v) :=
  exactTypeModel (LetIter.ProofRelevant.Semantics.Categorical.ofTypeModel (τ := τ))

variable {Φ : Type w} [HasTy Φ τ] {ε : Type q} [HasEff Φ ε] [Bot ε]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]

/-- Embed the given instruction interpretations as Kleisli arrows. -/
@[reducible] noncomputable def kleisliInstructionModel :
    LetIter.Semantics.Categorical.InstructionModel (Kleisli.Adjunction.toKleisli (ofTypeMonad m))
      (kleisliTypeModel τ) Φ :=
  letI := LetIter.ProofRelevant.Semantics.Categorical.ofInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  exactInstructionModel (Kleisli.Adjunction.toKleisli (ofTypeMonad m))
    (LetIter.ProofRelevant.Semantics.Categorical.ofTypeModel (τ := τ))

end Silmaril.Isotope.LetParIter.Categorical
