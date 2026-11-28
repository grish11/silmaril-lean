module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Mixed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.PartialFold.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.MixedTables
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.MixedSeparation

/-! # Mixed tables: duplication in one class, backedges across classes

A fan has one state running `q` and `K + 1` states running `p`. Every
repeat crosses between the two classes. The partial fold collapses the
duplicated class and leaves the other state in place.

The equations are derived in `WithPhaseUniformity` with no added seed. The
separation is computed in the four-reply interpreter and is used only to
refute an equation.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (event Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K' : Nat}

/-- A fan entered at any state equals the two-state table entered at the
state's class. The rows `q` and `p` are arbitrary written programs. -/
theorem Table.fan_eqv (K : Nat) (q p : Program) (j : Fin (K + 1)) (i : Fin (K + 2)) :
    Eqv false [State] ((Table.fan K q p j).entered i) ((Table.pingPong q p).entered (collapse i)) [Bit] :=
  Tables.fan_eqv K q p j i

/-- Two fans that differ in the number of duplicates and in the duplicate
the first state repeats into are equal when entered in the same class. -/
theorem Table.fan_eqv_fan (q p : Program) (j : Fin (K + 1)) (j' : Fin (K' + 1))
    (i : Fin (K + 2)) (i' : Fin (K' + 2)) (same : collapse i = collapse i') :
    Eqv false [State] ((Table.fan K q p j).entered i) ((Table.fan K' q p j').entered i') [Bit] :=
  (Table.fan_eqv K q p j i).trans (same ▸ (Table.fan_eqv K' q p j' i').symm)

/-- In a table of polls with one common label, every request of every
complete run carries that label. -/
theorem Table.labels (t : Table K) (poll : Fin (K + 1) → Poll) (l : Bool)
    (hprog : ∀ i, t.prog i = (poll i).program) (hl : ∀ i, (poll i).label = l)
    (i : Fin (K + 1)) (g : Bool) {obs : Except Bool (value Bit) × Word}
    (h : obs ∈ t.observations i g) : ∀ e ∈ FreeMonoid.toList obs.2, e.label = l :=
  TableModel.labels t poll l hprog hl i g h

/-- A run through the cross-class backedge: `q` repeats, `p` returns. -/
theorem pingPong_witness (q p : Poll) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event q.label g (!q.returnRight, s)) *
      FreeMonoid.of (event p.label s (p.returnRight, c))) ∈
      (Table.pingPong q.program p.program).observations 0 g :=
  TableModel.pingPong_witness q p g s c

/-- Changing the second class leaves the first round as it was. -/
theorem pingPong_first_round (q p p' : Program) (s : value State) :
    (Table.pingPong q p').stepM (injVal 1 0 s) = (Table.pingPong q p).stepM (injVal 1 0 s) :=
  (Table.step_run (Table.pingPong q p') 0 s).trans (Table.step_run (Table.pingPong q p) 0 s).symm

/-- A second class with another label separates only after the backedge. -/
theorem pingPong_ne {q p p' : Poll} (same : q.label = p.label) (other : p'.label ≠ p.label) :
    ¬ Eqv false [State] ((Table.pingPong q.program p'.program).entered 0)
      ((Table.pingPong q.program p.program).entered 0) [Bit] :=
  TableModel.pingPong_ne same other

/-- The same separation between fans of any sizes. -/
theorem Table.fan_ne {q p p' : Poll} (same : q.label = p.label) (other : p'.label ≠ p.label)
    (j : Fin (K + 1)) (j' : Fin (K' + 1)) :
    ¬ Eqv false [State] ((Table.fan K q.program p'.program j).entered 0)
      ((Table.fan K' q.program p.program j').entered 0) [Bit] :=
  fun e => pingPong_ne same other
    ((Table.fan_eqv K q.program p'.program j 0).symm.trans
      (e.trans (Table.fan_eqv K' q.program p.program j' 0)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
