module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.BlockParameters.Defs

/-! # Synthesizing outward transfers of typed CFG rows -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

/-- A written outward transfer uses an operand synthesizing `A` at index
`i` after the local label prefix. Both case arms contribute constraints. -/
def Row.exitsAt (i : Nat) (A : Ty κ) : {Δ : VCtx (Ty κ)} → Row (Φ := Φ) R L Δ → Prop
  | _, .jump .. => False
  | _, .exit (A := B) j _ _ => j = i ∧ B = A
  | _, .let₁ _ body => body.exitsAt i A
  | _, .let₂ _ body => body.exitsAt i A
  | _, .case _ left right => left.exitsAt i A ∨ right.exitsAt i A

/-- The row can supply an outward typing constraint whether or not it
reads the local block parameter. -/
def BlockParameters.Block.exitsAt {j : Fin n} (i : Nat) (A : Ty κ) :
    BlockParameters.Block (Φ := Φ) R L Γ j → Prop
  | .parameter row => row.exitsAt i A
  | .captured row => row.exitsAt i A

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
