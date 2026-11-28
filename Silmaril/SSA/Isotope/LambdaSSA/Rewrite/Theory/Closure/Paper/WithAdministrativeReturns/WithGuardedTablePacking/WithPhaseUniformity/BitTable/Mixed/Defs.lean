module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Defs

/-! # Mixed tables with backedges across two classes of states -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)

/-- State zero runs `q` and repeats into state `j + 1`. Each of the
`K + 1` later states runs `p` and repeats into state zero. Every repeat
crosses between the two classes. -/
def Table.fan (K : Nat) (q p : Program) (j : Fin (K + 1)) : Table (K + 1) :=
  ⟨Fin.cases q (fun _ => p), Fin.cases j.succ (fun _ => 0)⟩

/-- The table with one state in each class. -/
def Table.pingPong (q p : Program) : Table 1 := Table.fan 0 q p 0

/-- Forget which duplicate of the second class a state is. -/
def collapse {K : Nat} : Fin (K + 2) → Fin 2 := Fin.cases 0 (fun _ => 1)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
