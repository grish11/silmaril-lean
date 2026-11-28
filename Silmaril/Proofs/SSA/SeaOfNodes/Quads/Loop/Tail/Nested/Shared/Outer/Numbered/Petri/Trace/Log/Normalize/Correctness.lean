module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Lists
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Commutation.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Thms
import Mathlib.Data.List.Chain

public section
set_option backward.isDefEq.respectTransparency false

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Normalize.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (Fire pending finished)
open RVSDG.NestedTheta.Petri.Replay (checkFire checkFire_complete markingDecEq)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model) (roots : List (RootMark p))

local notation "start" => pending semantics (emitted p)
local notation "preStart" => pending semantics (preheader p)
local notation "tailStart" => pending semantics (entryTail p)
local notation "lastRoot" => roots.getLastD start

private theorem pending_rest : (entryCut p).rest semantics start = tailStart :=
  (congrArg ((entryCut p).rest semantics) ((entryCut p).attach_pending semantics).symm).trans
    ((entryCut p).rest_attach semantics preStart tailStart)

private theorem prefix_last :
    (prefixFirst p roots).getLastD start = (entryCut p).attach semantics (finalPreheader p roots) tailStart := by
  let _ := markingDecEq semantics colourEq (preheader p)
  have last : (prefixChanges p roots).getLastD preStart = finalPreheader p roots :=
    (congrArg (prefixChanges p roots).getLastD ((entryCut p).observe_pending semantics).symm).trans
      (changes_last ((entryCut p).observe semantics) start roots)
  let lift : PreMark p → RootMark p := fun pre => (entryCut p).attach semantics pre tailStart
  have pendingEq : lift preStart = start := (entryCut p).attach_pending semantics
  calc
    _ = ((prefixChanges p roots).map lift).getLastD (lift preStart) :=
      congrArg (List.getLastD ((prefixChanges p roots).map lift)) pendingEq.symm
    _ = lift ((prefixChanges p roots).getLastD preStart) := List.getLastD_map
    _ = _ := congrArg lift last

theorem final_eq :
    (normalize p roots).getLastD start = lastRoot := by
  let _ := markingDecEq semantics colourEq (entryTail p)
  have last : (thetaChanges p roots).getLastD tailStart = (entryCut p).rest semantics lastRoot :=
    (congrArg (thetaChanges p roots).getLastD (pending_rest p).symm).trans
      (changes_last ((entryCut p).rest semantics) start roots)
  unfold normalize thetaAfter
  rw [last_append, prefix_last, List.getLastD_map, last]
  exact (entryCut p).attach_observe_rest semantics lastRoot

private theorem prefix_legal (legal : List.IsChain (RootFire p input) (start :: roots)) :
    List.IsChain (ProfileStep p input) (start :: prefixFirst p roots) := by
  let _ := markingDecEq semantics colourEq (preheader p)
  have chain : List.IsChain (Fire semantics (preheader p) input PUnit.unit)
      (preStart :: prefixChanges p roots) := by
    rw [← (entryCut p).observe_pending semantics]
    exact changes_chain ((entryCut p).observe semantics)
      (fun step _ => match (entryCut p).split_step semantics input PUnit.unit step with
        | .inl ⟨fire, _⟩ => .inr fire
        | .inr ⟨same, _⟩ => .inl same) start roots legal rfl
  let lift : PreMark p → RootMark p := fun pre => (entryCut p).attach semantics pre tailStart
  have pendingEq : lift preStart = start := (entryCut p).attach_pending semantics
  have lifted : List.IsChain (ProfileStep p input) (lift preStart :: prefixFirst p roots) := by
    apply List.isChain_cons_map_of_isChain_cons lift _ chain
    intro a b step
    refine ⟨(entryCut p).lift_prefix_step semantics input PUnit.unit step tailStart, ?_⟩
    intro _ entered
    have h : (entryCut p).rest semantics (lift b) = tailStart :=
      (entryCut p).rest_attach semantics b tailStart
    unfold thetaPending at entered
    rw [h] at entered
    contradiction
  exact pendingEq ▸ lifted

private theorem tail_legal (legal : List.IsChain (RootFire p input) (start :: roots))
    (ready : (finished semantics (preheader p) input PUnit.unit (finalPreheader p roots)).isSome) :
    List.IsChain (ProfileStep p input) ((entryCut p).attach semantics (finalPreheader p roots) tailStart ::
      thetaAfter p roots) := by
  let _ := markingDecEq semantics colourEq (entryTail p)
  have chain : List.IsChain
      (Fire semantics (entryTail p) input ((entryCut p).tokens semantics PUnit.unit (finalPreheader p roots)))
      (tailStart :: thetaChanges p roots) := by
    rw [← pending_rest p]
    refine changes_chain ((entryCut p).rest semantics) (final := roots.getLastD start) ?_ start roots legal rfl
    intro a b step remaining
    rcases (entryCut p).split_step semantics input PUnit.unit step with ⟨_, same⟩ | ⟨_, fire⟩
    · exact .inl same
    · exact .inr ((entryCut p).tail_after_prefix semantics input PUnit.unit
        ((entryCut p).observe_reaches semantics input PUnit.unit remaining) fire)
  unfold thetaAfter
  apply List.isChain_cons_map_of_isChain_cons _ _ chain
  intro a b step
  refine ⟨(entryCut p).lift_tail_step semantics input PUnit.unit _ step, fun _ _ => ?_⟩
  rwa [(entryCut p).observe_attach]

theorem legal_complete (legal : List.IsChain (RootFire p input) (start :: roots))
    (done : (finished semantics (emitted p) input PUnit.unit lastRoot).isSome) :
    LegalComplete p input (normalize p roots) := by
  obtain ⟨_, returned⟩ := Option.isSome_iff_exists.mp done
  obtain ⟨_, ready⟩ := (entryCut p).completed_prefix semantics input lastRoot returned
  have tail := tail_legal p input roots legal (Option.isSome_iff_exists.mpr ⟨_, ready⟩)
  rw [← prefix_last p roots] at tail
  exact ⟨chain_append (prefix_legal p input roots legal) tail,
    (congrArg (fun mark => (finished semantics (emitted p) input PUnit.unit mark).isSome)
      (final_eq p roots)).symm ▸ done⟩

theorem theta_eq : thetaChanges p (normalize p roots) = thetaChanges p roots := by
  let _ := markingDecEq semantics colourEq (entryTail p)
  calc
    _ = changes ((entryCut p).rest semantics) start (thetaAfter p roots) := by
      unfold thetaChanges normalize
      apply changes_const
      intro mark mem
      obtain ⟨pre, _, rfl⟩ := List.mem_map.mp mem
      exact ((entryCut p).rest_attach semantics pre tailStart).trans (pending_rest p).symm
    _ = changes id ((entryCut p).rest semantics start) (thetaChanges p roots) :=
      changes_section ((entryCut p).rest semantics) ((entryCut p).attach semantics (finalPreheader p roots))
        ((entryCut p).rest_attach semantics (finalPreheader p roots)) start _
    _ = _ := changes_twice ((entryCut p).rest semantics) start roots

theorem scan_rejects_early {before after : RootMark p}
    (earlier later : List (RootMark p)) (atStep : start :: roots = earlier ++ before :: after :: later)
    (wasPending : thetaPending p before = true) (entered : thetaPending p after = false)
    (incomplete : finished semantics (preheader p) input PUnit.unit ((entryCut p).observe semantics after) = none) :
    (scan p input roots).isSome = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have chain := ((scan_isSome_iff p input roots).mp accepted).1
  rw [atStep] at chain
  have step := (List.isChain_cons_cons.mp chain.right_of_append).1
  have ready := step.2 wasPending entered
  rw [incomplete] at ready
  contradiction

private theorem check_steps (first : RootMark p) (marks : List (RootMark p)) :
    checkSteps p input first marks ↔ List.IsChain (RootFire p input) (first :: marks) := by
  induction marks generalizing first with
  | nil => exact ⟨fun _ => .singleton _, fun _ => rfl⟩
  | cons next tail ih =>
    have firing : (checkFire semantics colourEq (emitted p) input PUnit.unit first next).isSome ↔
        RootFire p input first next :=
      ⟨fun checked => (Option.isSome_iff_exists.mp checked).choose.down,
        checkFire_complete semantics colourEq⟩
    rw [checkSteps, Bool.and_eq_true, List.isChain_cons_cons, firing, ih next]

theorem scan_normalized_iff : (scanNormalized p input roots).isSome ↔ FireComplete p input roots := by
  let precheck := checkSteps p input start roots
  let done := (finished semantics (emitted p) input PUnit.unit lastRoot).isSome
  have checked : precheck && done ↔ FireComplete p input roots := by
    show (precheck && done) = true ↔ _
    rw [Bool.and_eq_true]
    exact and_congr (check_steps p input start roots) Iff.rfl
  unfold scanNormalized
  change (if precheck && done then scan p input (normalize p roots) else none).isSome ↔ _
  split
  · rename_i passed
    have legal := checked.mp passed
    exact ⟨fun _ => legal, fun _ => (scan_isSome_iff p input _).mpr
      (legal_complete p input roots legal.1 legal.2)⟩
  · rename_i failed
    exact ⟨fun impossible => Bool.noConfusion impossible, fun legal => False.elim (failed (checked.mpr legal))⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Normalize.Proofs
