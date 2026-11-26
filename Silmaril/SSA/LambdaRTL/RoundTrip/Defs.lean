module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Basic

/-! Assign names in the original register type to the finite support of a versioned region. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.RoundTrip

universe w

variable {V : Type w} [DecidableEq V] [Infinite V]

/-- An infinite supply disjoint from the base names of the versioned support. -/
noncomputable def freshNames (support : Finset (V × ℕ)) :
    ℕ ↪ ↥((↑(support.image Prod.fst) : Set V)ᶜ) :=
  @Infinite.natEmbedding _ (Set.Finite.infinite_compl (support.image Prod.fst).finite_toSet).to_subtype

/-- Keep every version-zero name. Each nonzero version in the support gets a
distinct fresh name outside the base names of the support. -/
noncomputable def deversion (support : Finset (V × ℕ)) (name : V × ℕ) : V :=
  if name.2 = 0 then name.1
  else if member : name ∈ support then
    (freshNames support (support.equivFin ⟨name, member⟩)).val
  else name.1

end Silmaril.SSA.LambdaRTL.RoundTrip
