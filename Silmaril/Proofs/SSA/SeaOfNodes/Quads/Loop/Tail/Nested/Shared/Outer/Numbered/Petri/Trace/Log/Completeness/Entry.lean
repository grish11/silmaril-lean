module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Activations
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Phases
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Waiting
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Mathlib.Data.List.Chain

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta (Graph Term)
open RVSDG.NestedTheta.Petri (Fire finished pending finishes_term_iff finishes_iff)
open RVSDG.NestedTheta.Petri.Replay (checkFire checkFire_complete)
open Relation (ReflTransGen)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

local notation "rootStart" => pending semantics (emitted p)
local notation "entryValue" => entryBank (src := src) (entry := entry) input
local notation "baseCode" => entryCode (src := src) (entry := entry)

private theorem preheader_run (fuel : Nat) :
    (preheader p).toGraph.run semantics fuel input = some entryValue := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph]
  change (Term.ofBase baseCode).run semantics fuel input = _
  rw [Term.run_ofBase]
  unfold RVSDG.Term.run entryCode entryBank
  erw [Join.Block.lowerFrom_eval, read_initial]
  rfl

private theorem preheader_exact {after : RootMark p}
    (reaches : ReflTransGen (RootFire p input) rootStart after)
    (complete : (finished semantics (preheader p) input PUnit.unit ((entryCut p).observe semantics after)).isSome) :
    finished semantics (preheader p) input PUnit.unit ((entryCut p).observe semantics after) = some entryValue := by
  let cut := entryCut p
  obtain ⟨bank, done⟩ := Option.isSome_iff_exists.mp complete
  have projected := cut.observe_reaches semantics input PUnit.unit reaches
  have preReaches : ReflTransGen (Fire semantics (preheader p) input PUnit.unit)
      (pending semantics (preheader p)) (cut.observe semantics after) :=
    cut.observe_pending semantics ▸ projected
  have finishes := (finishes_term_iff semantics (preheader p) input bank).mpr ⟨_, preReaches, done⟩
  obtain ⟨fuel, run⟩ := (finishes_iff semantics (preheader p).toGraph input bank).mp finishes
  exact done.trans (run.symm.trans (preheader_run p input fuel))

private theorem selected_bank {after : RootMark p} {bank : Bank (regs := regs) model}
    (done : finished semantics (preheader p) input PUnit.unit ((entryCut p).observe semantics after) = some entryValue)
    (read : RVSDG.Petri.read (endWires baseCode) input ((entryCut p).tokens semantics PUnit.unit
          ((entryCut p).observe semantics after)) = some bank) :
    bank = entryValue := by
  have published := (entryCut p).read_after semantics input PUnit.unit _ entryValue done
  change RVSDG.Petri.read (baseCut baseCode _).wires input _ = some entryValue at published
  rw [Petri.Proofs.base_cut_wires] at published
  exact Option.some.inj (read.symm.trans published)

private theorem enter_complete (start : RootMark p) (roots : List (RootMark p))
    (reaches : ReflTransGen (RootFire p input) rootStart start)
    (isPending : thetaPending p start = true)
    (legal : List.IsChain (ProfileStep p input) (start :: roots))
    (completed : (finished semantics (emitted p) input PUnit.unit (roots.getLastD start)).isSome) :
    (enter? p input start roots).isSome := by
  induction roots generalizing start with
  | nil => exact False.elim (pending_not_finished p input isPending completed)
  | cons after rest ih =>
    obtain ⟨⟨fires, profile⟩, later⟩ := List.isChain_cons_cons.mp legal
    obtain ⟨proof, checked⟩ := Option.isSome_iff_exists.mp (checkFire_complete semantics colourEq fires)
    rw [List.getLastD_cons] at completed
    have nextReaches := reaches.tail fires
    rcases from_pending p input isPending fires with stays | ⟨bank, read, fresh⟩
    · obtain ⟨piece, parsed⟩ := Option.isSome_iff_exists.mp (ih after nextReaches stays later completed)
      simp [enter?, checked, pending_cell p stays, parsed]
    · have entered := (congrArg (thetaPending p) fresh).trans (fresh_not_pending p _ _ _)
      have ready := preheader_exact p input nextReaches (profile isPending entered)
      have same := selected_bank p input ready read
      subst bank
      have target := (congrArg ((entryCut p).rest semantics) fresh).trans
        ((entryCut p).rest_attach semantics ((entryCut p).observe semantics after)
          (.waiting (0 : Fin 1) (entryValue, pending semantics (thetaBody p)), PUnit.unit))
      simp only [enter?, checked, bind, Option.bind, target]
      rw [dite_eq_left ready, dite_eq_left fresh]
      rfl

theorem scan_complete (roots : List (RootMark p)) (h : LegalComplete p input roots) :
    (scan p input roots).isSome := by
  obtain ⟨entered, parsed⟩ := Option.isSome_iff_exists.mp
    (enter_complete p input rootStart roots .refl (start_pending p) h.1 h.2)
  let first := atBody p entered.pre entryValue (pending semantics (thetaBody p))
  have original : List.IsChain (RootFire p input) (rootStart :: roots) := h.1.imp fun _ _ edge => edge.1
  have tail : List.IsChain (RootFire p input) (first :: entered.remaining) := by
    apply List.IsChain.right_of_append (l₁ := rootStart :: entered.earlier)
    rw [List.cons_append, ← entered.split]
    exact original
  have last : roots.getLastD rootStart = entered.remaining.getLastD first :=
    (congrArg (fun (marks : List (RootMark p)) => marks.getLastD rootStart) entered.split).trans (last_after_append _ _ _ _)
  have bound : entered.remaining.length ≤ roots.length := by
    have lengths := congrArg List.length entered.split
    simp only [List.length_append, List.length_cons] at lengths
    omega
  obtain ⟨rest, checked⟩ := Option.isSome_iff_exists.mp
    (recover_complete p input entered.complete roots.length entryValue entered.remaining bound tail (last ▸ h.2))
  simp [scan, parsed, checked]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs
