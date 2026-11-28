module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Thms

/-! # Single-exit, outward-join native ΛSSA -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

universe u v

variable {Φ : Type u}

/-- A predicate on written native regions. A one-row CFG enters its local row
at label zero, and that row transfers only to the selected outer exit.
The row can itself contain outward joins. Operands retain all native syntax. -/
inductive Outward : Nat → Region Φ → Prop where
  | br {exit : Nat} (arg : Tm Φ) : Outward exit (.br exit arg)
  | let₁ {exit : Nat} {r : Region Φ} (arg : Tm Φ) :
      Outward exit r → Outward exit (.let₁ arg r)
  | let₂ {exit : Nat} {r : Region Φ} (arg : Tm Φ) :
      Outward exit r → Outward exit (.let₂ arg r)
  | case {exit : Nat} {l r : Region Φ} (arg : Tm Φ) :
      Outward exit l → Outward exit r → Outward exit (.case arg l r)
  | join {exit : Nat} {entry : Region Φ} {blocks : Fin 1 → Region Φ} :
      Outward 0 entry → Outward (exit + 1) (blocks 0) → Outward exit (.cfg entry 1 blocks)

/-- An original native region at its exact single-exit interface. -/
structure Endpoint {τ : Type v} [TypeFormers τ] (Φ : Type u) [HasTy Φ τ]
    {n : Nat} (β : BoundCtx τ n) (A : τ) where
  region : Region Φ
  typed : Region.HasType β.toList region [A]
  outward : Outward 0 region

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
