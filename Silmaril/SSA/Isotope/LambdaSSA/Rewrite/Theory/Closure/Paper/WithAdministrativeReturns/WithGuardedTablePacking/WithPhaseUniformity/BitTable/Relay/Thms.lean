module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Relay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Mixed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.PartialFold.Feedback.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RelayTables
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RelayModel

/-! # A mixed table with an internal repeat in the untouched state

The untouched state repeats into itself on one reply side and enters the
duplicated block on the other. The block returns outward or repeats into
the untouched state. So the untouched block has its own feedback and the
feedback across the two blocks is reachable.

The equations are derived in `WithPhaseUniformity` by
`partial_fold_feedback`. The separation is computed in the four-reply
interpreter and only refutes an equation. Validity in every model follows
from the equations by soundness and is not used to obtain them.
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

/-! ## Collapse of the duplicated block -/

/-- A relay table entered at any state equals the two-state relay table
entered at the state's class. `q` and `p` are arbitrary written programs. -/
theorem relayFan_eqv (K : Nat) (q p : Program) (j : Fin (K + 1)) (i : Fin (K + 2)) :
    Eqv false [State] (relayFan K q p j i) (relayFan 0 q p 0 (collapse i)) [Bit] :=
  Tables.relayFan_eqv K q p j i

/-- Two relay tables that differ in the number of duplicates and in the
duplicate entered from the untouched state are equal in each class. -/
theorem relayFan_eqv_fan (q p : Program) (j : Fin (K + 1)) (j' : Fin (K' + 1))
    (i : Fin (K + 2)) (i' : Fin (K' + 2)) (same : collapse i = collapse i') :
    Eqv false [State] (relayFan K q p j i) (relayFan K' q p j' i') [Bit] :=
  (relayFan_eqv K q p j i).trans (same ▸ (relayFan_eqv K' q p j' i').symm)

/-- Hence they are valid in every supported model. -/
theorem relayFan_valid (q p : Program) (j : Fin (K + 1)) (j' : Fin (K' + 1))
    (i : Fin (K + 2)) (i' : Fin (K' + 2)) (same : collapse i = collapse i') :
    Valid (relayFan_typed K q p j i).hasType (relayFan_typed K' q p j' i').hasType :=
  valid_of_eqv false (relayFan_eqv_fan q p j j' i i' same) _ _

/-! ## The fixed interpreter -/

theorem relayObservations_eq (K : Nat) (q p : Program) (j : Fin (K + 1)) (i : Fin (K + 2)) (g : Bool) :
    relayObservations K q p j i g =
      (Silmaril.Elgot.iter (m := Trace) (relayStepM K q p j) (injVal (K + 1) i (Sum.inl (bit g)))).outcomes :=
  TableModel.relay_obs_eq K q p j i g

/-- The untouched state runs `q`, then repeats into itself or enters the block. -/
theorem relayStep_zero (K : Nat) (q p : Program) (j : Fin (K + 1)) (s : value State) :
    relayStepM K q p j (injVal (K + 1) 0 s) =
      Bind.bind (m := Trace) (stepModel q s) (relayRouteVal (K + 1) 0 j.succ) :=
  TableModel.relay_step_zero K q p j s

/-- A block state runs `p`, then returns outward or repeats into the untouched state. -/
theorem relayStep_succ (K : Nat) (q p : Program) (j : Fin (K + 1)) (i : Fin (K + 1)) (s : value State) :
    relayStepM K q p j (injVal (K + 1) i.succ s) =
      Bind.bind (m := Trace) (stepModel p s) (routeVal (K + 1) 0) :=
  TableModel.relay_step_succ K q p j i s

/-- A run with the internal repeat first: the untouched state repeats into
itself, then enters the block, where the second poll returns. -/
theorem relay_self_witness (q p : Poll) (g s s' c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event q.label g (q.returnRight, s)) *
      (FreeMonoid.of (event q.label s (!q.returnRight, s')) *
        FreeMonoid.of (event p.label s' (p.returnRight, c)))) ∈
      relayObservations 0 q.program p.program 0 0 g :=
  TableModel.relay_self_witness q p g s s' c

/-! ## Separation after the backedge -/

/-- Changing the block leaves every round of the untouched state as it was. -/
theorem relay_first_round (K : Nat) (q p p' : Program) (j : Fin (K + 1)) (s : value State) :
    relayStepM K q p' j (injVal (K + 1) 0 s) = relayStepM K q p j (injVal (K + 1) 0 s) :=
  (relayStep_zero K q p' j s).trans (relayStep_zero K q p j s).symm

/-- A run through the cross-block edge. -/
theorem relay_witness (q p : Poll) (g s c : Bool) :
    (Except.ok (bit c), FreeMonoid.of (event q.label g (!q.returnRight, s)) *
      FreeMonoid.of (event p.label s (p.returnRight, c))) ∈
      relayObservations 0 q.program p.program 0 0 g :=
  TableModel.relay_witness q p g s c

/-- With one common label, every request of every complete run carries it. -/
theorem relay_labels (K : Nat) (j : Fin (K + 1)) (q p : Poll) (l : Bool) (hq : q.label = l)
    (hp : p.label = l) (i : Fin (K + 2)) (g : Bool) {obs : Except Bool (value Bit) × Word}
    (h : obs ∈ relayObservations K q.program p.program j i g) :
    ∀ e ∈ FreeMonoid.toList obs.2, e.label = l :=
  TableModel.relay_labels K j q p l hq hp i g h

/-- A block with another label is separated, and only after the cross-block edge. -/
theorem relay_ne {q p p' : Poll} (same : q.label = p.label) (other : p'.label ≠ p.label) :
    ¬ Eqv false [State] (relayFan 0 q.program p'.program 0 0) (relayFan 0 q.program p.program 0 0) [Bit] :=
  TableModel.relay_ne same other

/-- The same separation between relay tables of any sizes. -/
theorem relayFan_ne {q p p' : Poll} (same : q.label = p.label) (other : p'.label ≠ p.label)
    (j : Fin (K + 1)) (j' : Fin (K' + 1)) :
    ¬ Eqv false [State] (relayFan K q.program p'.program j 0) (relayFan K' q.program p.program j' 0) [Bit] :=
  fun e => relay_ne same other
    ((relayFan_eqv K q.program p'.program j 0).symm.trans (e.trans (relayFan_eqv K' q.program p.program j' 0)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
