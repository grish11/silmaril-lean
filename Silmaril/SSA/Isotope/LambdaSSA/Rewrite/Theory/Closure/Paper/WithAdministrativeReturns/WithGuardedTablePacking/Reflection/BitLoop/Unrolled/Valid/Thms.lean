module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Unrolled.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Unrolling.Valid.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Reduction

/-! # Unrolled Bit loops are valid at every round count

For five rounds and every other count not covered by the quotient laws,
this gives validity in every supported model while the quotient equation
stays open. Nothing here derives a quotient equation.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking (Valid.symm Valid.trans)

variable {p q : Program} {a b : Poll}

/-- Every unrolled loop of the fragment is valid against the one-round loop. -/
theorem unrolled_valid (p : Program) (n : Nat) :
    Valid (unrolled_typed p n).hasType (loop_typed p).hasType :=
  valid_unrolled false (step_typed p) n

/-- The literal five-round polling pair. -/
theorem Poll.fiveRounds_valid (a : Poll) :
    Valid (unrolled_typed a.program 4).hasType (loop_typed a.program).hasType :=
  unrolled_valid a.program 4

/-- Validity of two unrolled loops is validity of the one-round loops, at
any two round counts. -/
theorem unrolled_valid_iff (p q : Program) (m n : Nat) :
    Valid (unrolled_typed p m).hasType (unrolled_typed q n).hasType ↔
      Valid (loop_typed p).hasType (loop_typed q).hasType :=
  ⟨fun h => Valid.trans (Valid.symm (unrolled_valid p m)) (Valid.trans h (unrolled_valid q n)),
    fun h => Valid.trans (unrolled_valid p m) (Valid.trans h (Valid.symm (unrolled_valid q n)))⟩

/-- On spellings of polls, validity at any two round counts is equality
of the one-round keys. -/
theorem unrolled_valid_iff_key (hp : Spells p a) (hq : Spells q b) (m n : Nat) :
    Valid (unrolled_typed p m).hasType (unrolled_typed q n).hasType ↔ p.tree.key = q.tree.key :=
  (unrolled_valid_iff p q m n).trans (valid_iff_key hp hq)

/-- Reflection at an unrolled loop and its one-round loop is exactly the
quotient equation between them. -/
theorem unrolled_reflects_iff (p : Program) (n : Nat) :
    Reflects false (unrolled_typed p n) (loop_typed p) ↔
      Eqv false [State] (unrolled p n) (loopRegion p) [Bit] :=
  ⟨fun h => h (unrolled_valid p n), fun e _ => e⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
