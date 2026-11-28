module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live.Defs

/-! # A live table with two exits of one payload type -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Live

open Silmaril Silmaril.Isotope.LambdaSSA
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live

/-- Both exits carry a payload. Their written order distinguishes them. -/
abbrev Exits : LCtx (Ty Atom) := [Payload, Payload]

/-- A payload reply leaves by the first exit. A unit reply enters the second row. -/
def firstRow : Region Op :=
  .let₁ (.op .poll (.var 0)) (.case (.var 0) (.br 1 (.var 0)) (.br 2 (.var 0)))

/-- Poll the retained input. A unit reply returns it to the first row and
a payload reply leaves by the second exit. -/
def secondRow : Region Op :=
  .let₁ (.op .poll (.var 1)) (.case (.var 0) (.br 0 (.var 3)) (.br 3 (.var 0)))

def twoExitRows : Fin 2 → Region Op := fun i => if i.val = 0 then firstRow else secondRow

def twoExit : Region Op := .cfg entry 2 twoExitRows

theorem twoExit_entry_typed : ValueBranches [Payload] entry (List.ofFn labels ++ Exits) :=
  .let₁ (.op (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var (i := 0) rfl))

theorem twoExit_rows_typed (i : Fin 2) :
    ValueBranches [labels i, Payload] (twoExitRows i) (List.ofFn labels ++ Exits) := by
  have row0 : ValueBranches [labels 0, Payload] (twoExitRows 0) (List.ofFn labels ++ Exits) :=
    .let₁ (.op (.var (i := 0) rfl)) (.case (.var (i := 0) rfl)
      (.br (ℓ := 1) rfl (.var (i := 0) rfl)) (.br (ℓ := 2) rfl (.var (i := 0) rfl)))
  have row1 : ValueBranches [labels 1, Payload] (twoExitRows 1) (List.ofFn labels ++ Exits) :=
    .let₁ (.op (.var (i := 1) rfl)) (.case (.var (i := 0) rfl)
      (.br (ℓ := 0) rfl (.var (i := 3) rfl)) (.br (ℓ := 3) rfl (.var (i := 0) rfl)))
  refine Fin.cases row0 (fun j => ?_) i
  have eq : j = 0 := Subsingleton.elim _ _
  exact eq.symm ▸ row1

theorem twoExit_typed : ValueBranches [Payload] twoExit Exits :=
  .cfg labels twoExit_entry_typed twoExit_rows_typed

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Live
