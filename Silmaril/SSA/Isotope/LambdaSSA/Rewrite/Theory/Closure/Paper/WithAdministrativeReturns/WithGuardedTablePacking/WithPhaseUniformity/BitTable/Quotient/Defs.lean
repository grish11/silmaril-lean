module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Defs

/-! # An uneven three-class table

`Table.cycle3` has three states `a → b → c → a`, each with its own
program.

`Table.uneven` has six states in the written order `c a c b c b`: one
duplicate of `a`, two of `b` and three of `c`, interleaved. Entered at
state five it passes through five different states:
`b₅ → c₂ → a₁ → b₃ → c₄ → a₁ → …`.

`Table.unevenWith` runs another program at state two, the `c` duplicate
reached after one backedge from state five.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)

/-- Three states in a cycle, each with its own program. -/
def Table.cycle3 (qa qb qc : Program) : Table 2 where
  prog i := match i with
    | 0 => qa
    | 1 => qb
    | 2 => qc
  next i := match i with
    | 0 => 1
    | 1 => 2
    | 2 => 0

/-- The classes of the six states: `c a c b c b`. -/
def unevenClass (i : Fin 6) : Fin 3 :=
  match i with
  | 0 => 2
  | 1 => 0
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 1

/-- The successors of the six states. -/
def unevenNext (i : Fin 6) : Fin 6 :=
  match i with
  | 0 => 1
  | 1 => 3
  | 2 => 1
  | 3 => 4
  | 4 => 1
  | 5 => 2

/-- The six-state table with the program `qd` at state two. -/
def Table.unevenWith (qa qb qc qd : Program) : Table 5 where
  prog i := match i with
    | 0 => qc
    | 1 => qa
    | 2 => qd
    | 3 => qb
    | 4 => qc
    | 5 => qb
  next := unevenNext

/-- The six-state table of the three classes. -/
def Table.uneven (qa qb qc : Program) : Table 5 := Table.unevenWith qa qb qc qc

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
