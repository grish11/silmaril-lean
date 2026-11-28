module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Paths.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.Typing

/-! # Propagating exact label types out of a nested CFG -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters

variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  {n : Nat} {R : Fin n → Ty κ} {L K : LCtx (Ty κ)} {Γ : VCtx (Ty κ)}

/-- Read the selected inner family from exact typing. A synthesizing jump
path fixes the input of the reached row, so the outward operand fixes the
type at its index in the actual boundary `K`. The row description's
boundary `L` can differ from `K`. Unreached inner slot types stay free. -/
theorem Program.outward_type_at_reached (p : Program (Φ := Φ) R L Γ) {j : Fin n} {i : Nat} {A : Ty κ}
    (path : p.Reaches j) (hit : (p.blocks j).exitsAt i A) (typed : p.region.HasType Γ K) : At K i A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.outward_type p path hit typed

/-- The inner outward interface starts with the enclosing CFG's locals.
An inner transfer to one of those indices forces that sibling's parameter
type, independently of the untargeted inner slots and the ordered exits. -/
theorem Program.enclosing_type_at_reached (p : Program (Φ := Φ) R L Γ) {m : Nat} {F : Fin m → Ty κ}
    {j : Fin n} (path : p.Reaches j) (i : Fin m) {A : Ty κ}
    (hit : (p.blocks j).exitsAt i A) (typed : p.region.HasType Γ (List.ofFn F ++ K)) : F i = A :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.UnusedSummandBlockParameters.enclosing_type
    p path i hit typed

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand.BlockParameters
