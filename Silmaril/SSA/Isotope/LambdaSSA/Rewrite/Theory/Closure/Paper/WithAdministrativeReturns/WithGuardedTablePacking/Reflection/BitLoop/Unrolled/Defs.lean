module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Unrolling.Thms

/-! # Written request loops with several rounds per iteration -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Rounds
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

/-- One feedback label around `n + 1` inline rounds of the step of `p`.
A round that returns leaves the loop. The last round's repeat takes the
backedge. This is a one-row guarded table with a constructor entry. -/
def unrolled (p : Program) (n : Nat) : Region signature.Instr :=
  SyntacticCategory.iterateRegion State (roundsRegion (stepRegion p) n)

theorem unrolled_typed (p : Program) (n : Nat) : ValueBranches [State] (unrolled p n) [Bit] :=
  SyntacticCategory.iterateRegion_valueBranches (roundsRegion_typed (step_typed p) n)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
