module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Readback.Defs

/-! # Exact CFG rows with parameter types propagated from the entry -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n : Nat} {R : Fin n → Ty κ} {L : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

/-- A parameter row may read its typed CFG parameter. A captured row skips
that parameter and uses the outer context. -/
inductive Block (R : Fin n → Ty κ) (L : LCtx (Ty κ)) (Γ : VCtx (Ty κ)) (i : Fin n) where
  | parameter (row : Row (Φ := Φ) R L (R i :: Γ))
  | captured (row : Row (Φ := Φ) R L Γ)

def Block.region {i : Fin n} : Block (Φ := Φ) R L Γ i → Region Φ
  | .parameter row => row.region false id
  | .captured row => row.region false Nat.succ

def Block.targets {i : Fin n} (j : Fin n) : Block (Φ := Φ) R L Γ i → Prop
  | .parameter row => row.targets j
  | .captured row => row.targets j

def Block.hasParameter {i : Fin n} : Block (Φ := Φ) R L Γ i → Prop
  | .parameter _ => True
  | .captured _ => False

/-- A native table with an entry, typed parameter-reading rows, and rows
whose syntax skips the CFG parameter. Jump payloads synthesize exact types. -/
structure Program (R : Fin n → Ty κ) (L : LCtx (Ty κ)) (Γ : VCtx (Ty κ)) where
  entry : Row (Φ := Φ) R L Γ
  blocks : ∀ i, Block (Φ := Φ) R L Γ i

def Program.region (p : Program (Φ := Φ) R L Γ) : Region Φ :=
  .cfg (p.entry.region false id) n (fun i => (p.blocks i).region)

def Program.targets (p : Program (Φ := Φ) R L Γ) (i : Fin n) : Prop :=
  p.entry.targets i ∨ ∃ j, (p.blocks j).targets i

/-- A finite path of written jumps from the entry. Both case arms count. -/
inductive Program.Reaches (p : Program (Φ := Φ) R L Γ) : Fin n → Prop where
  | entry {i} : p.entry.targets i → p.Reaches i
  | next {i j} : p.Reaches i → (p.blocks i).targets j → p.Reaches j

/-- Every written target has a typed path from the entry, and every block
admitted to read its parameter has such a path. This allows rooted cycles.
The first field lets rolling use the same inclusion for all row transfers. -/
structure Program.ReachableParameters (p : Program (Φ := Φ) R L Γ) : Prop where
  targets : ∀ i, p.targets i → p.Reaches i
  parameters : ∀ i, (p.blocks i).hasParameter → p.Reaches i

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters
