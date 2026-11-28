module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Dispatcher.Defs

/-! # An opt-in typed quotient that packs guarded tables

The added equation is separate from `Paper.Eqv` and from every quotient
below this one. It relates the two literal regions only.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking

open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open CategoryTheory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- A nonempty guarded table with one capture and one outward exit, and
its packed readback: the routed entry followed by one feedback label around
the ordered captured dispatcher. The left endpoint is the written table and
the right endpoint is the representative of `packedReadbackRep`. -/
inductive Pack : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop
  | table {n : Nat} (R : Fin (n + 1) → τ) {X D : τ} {e : Region Φ} {blocks : Fin (n + 1) → Region Φ}
      (he : ValueBranches [X] e (List.ofFn R ++ [D]))
      (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
      Pack [X] (.cfg e (n + 1) blocks) (packedReadbackRep R he hb).val [D]

/-- Keep every administrative-return seed and adjoin guarded table packing. -/
abbrev Step (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithAdministrativeReturns.Step pe Γ r s L ∨ Pack Γ r s L

abbrev Eqv := Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ) pe)
abbrev TypeCategory := Paper.Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ) pe)

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) (Φ := Φ) pe :=
  Paper.Extension.Singleton.projection (Step pe)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking
