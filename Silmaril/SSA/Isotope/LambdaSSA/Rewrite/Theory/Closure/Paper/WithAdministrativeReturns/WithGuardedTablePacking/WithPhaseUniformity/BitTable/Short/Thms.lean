module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Short.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Pair.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Composite.Padding.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ShortTables

/-! # Replay for a table with two and three duplicates

Class `a` has two duplicates and class `b` has three. The collapse uses
`pair_fold_short` with the one overall square for the five-state table.
The padding state and the padded table do not appear in the statements.

The separation reuses the relay table's and is computed in the four-reply
interpreter. It only refutes an equation.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

/-- The five-state table entered at any state equals the two-state relay
table entered at the state's class. `q`, `p` and the wiring are arbitrary. -/
theorem shortTable_eqv (q p : Program) (w : ShortWiring) (i : Fin 5) :
    Eqv false [State] (shortTable q p w i) (relayFan 0 q p 0 (shortClass i)) [Bit] :=
  Tables.shortTable_eqv q p w i

/-- Replay: two five-state tables with any wirings are equal in each class. -/
theorem shortTable_replay (q p : Program) (w w' : ShortWiring) (i i' : Fin 5)
    (same : shortClass i = shortClass i') :
    Eqv false [State] (shortTable q p w i) (shortTable q p w' i') [Bit] :=
  (shortTable_eqv q p w i).trans (same ▸ (shortTable_eqv q p w' i').symm)

/-- The five-state table against the four-state table of two and two
duplicates, in each class. -/
theorem shortTable_eqv_pairTable (q p : Program) (w : ShortWiring) (w' : Wiring) (i : Fin 5) (i' : Fin 4)
    (same : shortClass i = pairClass i') :
    Eqv false [State] (shortTable q p w i) (pairTable q p w' i') [Bit] :=
  (shortTable_eqv q p w i).trans (same ▸ (pairTable_eqv q p w' i').symm)

/-- Jumps spread over the duplicates against jumps to the first duplicate. -/
theorem spread_eqv_first (q p : Program) (i : Fin 5) :
    Eqv false [State] (shortTable q p ShortWiring.spread i) (shortTable q p ShortWiring.first i) [Bit] :=
  shortTable_replay q p _ _ i i rfl

/-- Validity in every supported model, as a consequence of the equation. -/
theorem shortTable_valid (q p : Program) (w w' : ShortWiring) (i i' : Fin 5)
    (same : shortClass i = shortClass i') :
    Valid (shortTable_typed q p w i).hasType (shortTable_typed q p w' i').hasType :=
  valid_of_eqv false (shortTable_replay q p w w' i i' same) _ _

/-- A class `b` with another label is separated, for any wirings, entered
at an `a` state. -/
theorem shortTable_ne {q p p' : Poll} (same : q.label = p.label) (other : p'.label ≠ p.label)
    (w w' : ShortWiring) :
    ¬ Eqv false [State] (shortTable q.program p'.program w 1) (shortTable q.program p.program w' 1) [Bit] :=
  fun e => relay_ne same other
    ((shortTable_eqv q.program p'.program w 1).symm.trans (e.trans (shortTable_eqv q.program p.program w' 1)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
