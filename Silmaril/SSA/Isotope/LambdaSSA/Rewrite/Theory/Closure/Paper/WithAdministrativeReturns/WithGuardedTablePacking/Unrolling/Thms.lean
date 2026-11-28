module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Rounds.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Unrolling

/-! # Unrolling by twos and threes in the table-packing quotient

No rule is added. The two-round law comes from the binary-fold seed and
the three-round law from the tripling seed, both already among the seeds
of this quotient. Round counts with another prime factor are not covered.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.Extension.Singleton.Rounds

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Two rounds of any step, effectful or not, iterate as one. -/
theorem doubles : Doubles (Step (τ := τ) (Φ := Φ) pe) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.doubles pe

/-- Three rounds of any step iterate as one. -/
theorem triples : Triples (Step (τ := τ) (Φ := Φ) pe) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.triples pe

theorem unrolls {n : Nat} (h : Smooth n) : Unrolls (Step (τ := τ) (Φ := Φ) pe) n :=
  unrolls_of_smooth _ (doubles pe) (triples pe) h

/-- The written loop on `n + 1` rounds of a guarded step equals the written
loop on one round, when `n + 1` is a product of twos and threes. -/
theorem unrolled_eqv {n : Nat} (h : Smooth n) {A B : τ} {s : Region Φ}
    (hs : ValueBranches [A] s [Silmaril.coprod B A]) :
    Eqv pe [A] (SyntacticCategory.iterateRegion A (roundsRegion s n))
      (SyntacticCategory.iterateRegion A s) [B] :=
  Paper.Extension.Singleton.Rounds.unrolled_eqv _ (unrolls pe h) hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking
