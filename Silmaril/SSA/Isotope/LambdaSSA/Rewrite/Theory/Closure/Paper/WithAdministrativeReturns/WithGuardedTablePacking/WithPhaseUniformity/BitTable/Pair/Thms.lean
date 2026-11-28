module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Pair.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Relay.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Composite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PairTables

/-! # Replay for a table with two duplicated classes

Both classes are duplicated, with a repeat inside class `a` and jumps in
both directions between the classes. Each duplicate chooses its own
target duplicates. The collapse uses `pair_fold` with the one overall
square `pair_square`. No intermediate table is used.

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

/-- The table with both classes duplicated, entered at any state, equals
the two-state relay table entered at the state's class. `q`, `p` and the
wiring are arbitrary. -/
theorem pairTable_eqv (q p : Program) (w : Wiring) (i : Fin 4) :
    Eqv false [State] (pairTable q p w i) (relayFan 0 q p 0 (pairClass i)) [Bit] :=
  Tables.pairTable_eqv q p w i

/-- Replay: two such tables with any wirings are equal when entered in
the same class. -/
theorem pairTable_replay (q p : Program) (w w' : Wiring) (i i' : Fin 4)
    (same : pairClass i = pairClass i') :
    Eqv false [State] (pairTable q p w i) (pairTable q p w' i') [Bit] :=
  (pairTable_eqv q p w i).trans (same ▸ (pairTable_eqv q p w' i').symm)

/-- Duplicates that target each other's duplicates, against duplicates
that all target the first. In the crossed table the two `b` states repeat
into different `a` states. -/
theorem crossed_eqv_first (q p : Program) (i : Fin 4) :
    Eqv false [State] (pairTable q p Wiring.crossed i) (pairTable q p Wiring.first i) [Bit] :=
  pairTable_replay q p _ _ i i rfl

/-- Hence validity in every supported model. It is a consequence of the
equation and is not used to obtain it. -/
theorem pairTable_valid (q p : Program) (w w' : Wiring) (i i' : Fin 4)
    (same : pairClass i = pairClass i') :
    Valid (pairTable_typed q p w i).hasType (pairTable_typed q p w' i').hasType :=
  valid_of_eqv false (pairTable_replay q p w w' i i' same) _ _

/-- A class `b` with another label is separated, for any wirings. The
first request is unchanged, and the separating run crosses into class `b`. -/
theorem pairTable_ne {q p p' : Poll} (same : q.label = p.label) (other : p'.label ≠ p.label)
    (w w' : Wiring) :
    ¬ Eqv false [State] (pairTable q.program p'.program w 0) (pairTable q.program p.program w' 0) [Bit] :=
  fun e => relay_ne same other
    ((pairTable_eqv q.program p'.program w 0).symm.trans (e.trans (pairTable_eqv q.program p.program w' 0)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
