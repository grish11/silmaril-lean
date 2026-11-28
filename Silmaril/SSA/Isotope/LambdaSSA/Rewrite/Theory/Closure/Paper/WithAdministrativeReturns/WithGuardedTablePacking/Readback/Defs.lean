module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Assembly.Thms

/-! # The captured readback comparison in the table-packing quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Paper.WithCaseReturns.BinaryFold.WithTripling (capturedDispatcher)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (entry_route orderedRows)
open Paper.Extension.Singleton (ofRegion ofType iterateSum)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Include the tripling quotient, which carries the captured dispatcher,
through computed calls, unary returns and administrative returns. -/
abbrev fromTripling :
    Paper.WithCaseReturns.BinaryFold.WithTripling.TypeCategory (τ := τ) (Φ := Φ) pe ⥤
      TypeCategory (τ := τ) (Φ := Φ) pe :=
  Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.fromWithTripling pe ⋙
    Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.fromWithComputedCalls pe ⋙
      WithAdministrativeReturns.fromUnaryReturns pe ⋙ fromAdministrativeReturns pe

/-- The comparison of `TableReadback.Readback`, read in this quotient: the
written table against its routed entry followed by the iterated captured
dispatcher assembled from the actual rows. -/
noncomputable def Readback {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin n → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) : Prop :=
  let N := Step (τ := τ) (Φ := Φ) pe
  let start := ofRegion N (entry_route R he)
  let step := (fromTripling pe).map (capturedDispatcher pe X (List.ofFn R) (orderedRows pe R hb))
  ofRegion N (.cfg R he hb) = start ≫ exactCopair N (𝟙 (ofType N D)) (iterateSum N step)

/-- Tag each outward exit of a table component with its written position.
The first `n` labels are the table's own rows and stay in place. -/
def tagExits (n : Nat) : Nat → Region Φ :=
  liftLSubstN n (fun i => .br 0 (packedExitArg i (.var 0)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking
