module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Simulation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableSeparation
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Reduction

/-! # Replay and separation for multi-state request tables

## Proved

* `Table.single_square`: when every state runs the same written program,
  the state fold is a simulation of the table onto that program, as an
  equation of default Paper.
* `Table.single_eqv`: hence the table, entered at any state and with any
  successor wiring, equals the one-row loop of the program in
  `WithPhaseUniformity`.
* `Table.replay`, `Table.eqv_iff_valid`, `Table.poll_eqv_iff`: on tables
  whose single program spells a poll, the quotient equation, validity in
  every supported model and equality of the program keys coincide. The two
  tables may differ in size, wiring and entry state.
* `handoff_ne`: a table that hands off to a different poll after its first
  backedge is not equal to the loop of its first poll. Its first round is
  that poll's round (`handoff_first_round`). The separating run has two
  requests (`handoff_witness`, `handoff_not_poll`).

## Not proved

* Tables whose states run different programs are not collapsed. That needs
  uniformity along a map that folds some states and keeps others, such as
  `id + fold`. The seed gives the total fold only, and no derivation of the
  partial case is given here.
* Rows are written as a program step followed by a routing case on its
  packed result. The spelling with direct jumps in the reply arms differs
  by case β under the request and is not related here.
* Equality in the fixed interpreter is used only to separate. No quotient
  equation is inferred from it, and nothing is claimed about packed
  dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion phaseFold sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K' : Nat} {p q : Program} {a b : Poll}

/-! ## Collapsing duplicated states -/

/-- The checked simulation: the state fold maps a single-program table
onto its program. This is an equation of default Paper. -/
theorem Table.single_square (t : Table K) (single : t.Single p) :
    (ofRegion t.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) (phaseFold State K) =
      phaseFold State K ≫ (ofRegion (WithGuardedTablePacking.BitLoop.step_typed p) ≫ (sumIso (Φ := signature.Instr) Bit State).hom) :=
  Tables.single_square t p single

/-- A single-program table entered at any state equals the one-row loop. -/
theorem Table.single_eqv (t : Table K) (single : t.Single p) (i : Fin (K + 1)) :
    Eqv false [State] (t.entered i) (loopRegion p) [Bit] :=
  Tables.single_eqv t p single i

/-- Two single-program tables whose programs spell polls are equal exactly
when the program keys agree. -/
theorem Table.replay {t : Table K} {t' : Table K'} (ht : t.Single p) (ht' : t'.Single q)
    (hp : Spells p a) (hq : Spells q b) (i : Fin (K + 1)) (i' : Fin (K' + 1)) :
    Eqv false [State] (t.entered i) (t'.entered i') [Bit] ↔ p.tree.key = q.tree.key :=
  ⟨fun h => (WithPhaseUniformity.BitLoop.replay hp hq 0 0).1
      ((t.single_eqv ht i).symm.trans (h.trans (t'.single_eqv ht' i'))),
    fun h => (t.single_eqv ht i).trans
      (((WithPhaseUniformity.BitLoop.replay hp hq 0 0).2 h).trans (t'.single_eqv ht' i').symm)⟩

/-- On that family the quotient equation is validity in every supported model. -/
theorem Table.eqv_iff_valid {t : Table K} {t' : Table K'} (ht : t.Single p) (ht' : t'.Single q)
    (hp : Spells p a) (hq : Spells q b) (i : Fin (K + 1)) (i' : Fin (K' + 1)) :
    Eqv false [State] (t.entered i) (t'.entered i') [Bit] ↔
      Valid (t.entered_typed i).hasType (t'.entered_typed i').hasType := by
  have left : Valid (t.entered_typed i).hasType (WithGuardedTablePacking.BitLoop.loop_typed p).hasType :=
    valid_of_eqv false (t.single_eqv ht i) _ _
  have right : Valid (t'.entered_typed i').hasType (WithGuardedTablePacking.BitLoop.loop_typed q).hasType :=
    valid_of_eqv false (t'.single_eqv ht' i') _ _
  refine ⟨fun h => valid_of_eqv false h _ _, fun v => ?_⟩
  exact (Table.replay ht ht' hp hq i i').2
    ((valid_iff_key hp hq).1 (Valid.trans (Valid.symm left) (Valid.trans v right)))

/-- Tables of polls are equal only when they run the same poll. -/
theorem Table.poll_eqv_iff {t : Table K} {t' : Table K'} (ht : t.Single a.program)
    (ht' : t'.Single b.program) (i : Fin (K + 1)) (i' : Fin (K' + 1)) :
    Eqv false [State] (t.entered i) (t'.entered i') [Bit] ↔ a = b :=
  ⟨fun h => (WithPhaseUniformity.BitLoop.Poll.unrolled_eqv_iff a b 0 0).1
      ((t.single_eqv ht i).symm.trans (h.trans (t'.single_eqv ht' i'))),
    fun h => by
      subst h
      exact (t.single_eqv ht i).trans (t'.single_eqv ht' i').symm⟩

/-- Two states that repeat into each other, against three states in a cycle. -/
theorem swap_eqv_cycle (p : Program) (i : Fin 2) (j : Fin 3) :
    Eqv false [State] ((Table.swap p).entered i) ((Table.cycle p).entered j) [Bit] :=
  ((Table.swap p).single_eqv (fun _ => rfl) i).trans ((Table.cycle p).single_eqv (fun _ => rfl) j).symm

/-! ## The fixed interpreter -/

/-- The table loop is the interpreter's iterator on the dispatcher step. -/
theorem Table.observations_eq (t : Table K) (i : Fin (K + 1)) (g : Bool) :
    t.observations i g =
      (Silmaril.Elgot.iter (m := Trace) t.stepM (injVal K i (Sum.inl (bit g)))).outcomes :=
  TableModel.observations_eq t i g

/-- At state `i` the dispatcher runs that row's program and routes its
result to the row's successor. -/
theorem Table.step_run (t : Table K) (i : Fin (K + 1)) (s : value State) :
    t.stepM (injVal K i s) =
      Bind.bind (m := Trace) (stepModel (t.prog i) s) (routeVal K (t.next i)) :=
  TableModel.step_run t i s

/-! ## Separation after a backedge -/

/-- The first round of a handoff table is the round of its first program.
Only the state it repeats into differs from the one-row loop. -/
theorem handoff_first_round (p q : Program) (s : value State) :
    (Table.handoff p q).stepM (injVal 1 0 s) =
      Bind.bind (m := Trace) (stepModel p s) (routeVal 1 1) :=
  (TableModel.step_run (Table.handoff p q) 0 s).trans
    (congrArg (fun r => Bind.bind (m := Trace) (stepModel r s) (routeVal 1 1))
      (TableModel.handoff_zero p q))

/-- A run through the backedge: the first poll repeats, the second returns. -/
theorem handoff_witness (a b : Poll) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event a.label g (!a.returnRight, s)) *
      FreeMonoid.of (event b.label s (b.returnRight, c))) ∈
      (Table.handoff a.program b.program).observations 0 g :=
  TableModel.handoff_witness a b g s c

/-- The one-row loop of the first poll has no such run when the polls differ. -/
theorem handoff_not_poll (ne : a ≠ b) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event a.label g (!a.returnRight, s)) *
      FreeMonoid.of (event b.label s (b.returnRight, c))) ∉ loopObservations a.program g :=
  TableModel.handoff_not_poll ne g s c

/-- So the handoff table is not equal to the loop of its first poll. -/
theorem handoff_ne (ne : a ≠ b) :
    ¬ Eqv false [State] ((Table.handoff a.program b.program).entered 0) (loopRegion a.program) [Bit] :=
  TableModel.handoff_ne ne

/-- Nor to any single-poll table of the first poll. -/
theorem handoff_ne_single (ne : a ≠ b) {t : Table K} (ht : t.Single a.program) (i : Fin (K + 1)) :
    ¬ Eqv false [State] ((Table.handoff a.program b.program).entered 0) (t.entered i) [Bit] :=
  fun e => handoff_ne ne (e.trans (t.single_eqv ht i))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
