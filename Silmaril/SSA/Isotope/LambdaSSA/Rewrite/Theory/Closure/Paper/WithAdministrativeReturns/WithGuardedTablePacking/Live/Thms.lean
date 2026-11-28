module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Live.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Readback.Thms

/-! # The separated live-table equations hold after opting in

`TableReadback.Live.readback_fails` and `constructorEntry_readback_fails`
refute these two comparisons in the unary-return quotient. Here both hold,
at the same written table and the same packed representative.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Live

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live

/-- The effectful written entry and reachable two-row table equal their
captured dispatcher readback. -/
theorem readback : Readback false labels entry_typed rows_typed :=
  WithGuardedTablePacking.readback false labels entry_typed rows_typed

/-- The same table equals its readback when the entry is one constructor branch. -/
theorem constructorEntry_readback :
    Readback false labels
      (.br (ℓ := 0) rfl (.var (i := 0) rfl : Tm.BranchValue [Payload] (.var 0 : Tm Op) Payload))
      rows_typed :=
  WithGuardedTablePacking.readback false labels _ rows_typed

/-- The contextual form of the first equation at the two literal regions. -/
theorem written_eqv_packed :
    Eqv false [Payload] written (packedReadbackRep labels entry_typed rows_typed).val [Result] :=
  pack false labels entry_typed rows_typed

/-- The two payload exits receive the tags of their written positions. -/
theorem twoExit_tags :
    (tagExits 2 2 : Region Op) = .br 2 (.inl (.var 0)) ∧
      (tagExits 2 3 : Region Op) = .br 2 (.inr (.inl (.var 0))) :=
  ⟨tagExits_outward 2 0, tagExits_outward 2 1⟩

/-- The table with two payload exits equals its decoded packed readback at
its written exits. -/
theorem twoExit_retraction :
    Eqv false [Payload] twoExit
      ((packedReadbackRep labels (tagExits_entry labels twoExit_entry_typed)
        (tagExits_row labels twoExit_rows_typed)).val.lsubst (fun _ => unpackExits Exits)) Exits :=
  retraction false labels twoExit_entry_typed twoExit_rows_typed

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Live
