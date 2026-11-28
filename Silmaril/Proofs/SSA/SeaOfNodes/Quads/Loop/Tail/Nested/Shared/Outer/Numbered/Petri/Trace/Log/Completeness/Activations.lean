module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Phases
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Thms
import Mathlib.Data.List.Chain

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finished pending)
open RVSDG.NestedTheta.Petri.Replay (checkFire checkFire_complete)
open Relation (ReflTransGen)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

theorem last_after_append {M : Type} (earlier remaining : List M) (start after : M) :
    (earlier ++ after :: remaining).getLastD start = remaining.getLastD after := by
  induction earlier generalizing start with
  | nil => exact List.getLastD_cons
  | cons _ _ ih => rw [List.cons_append, List.getLastD_cons, ih]

private theorem completed_latch {pre : PreMark p} {preBank old : Bank (regs := regs) model}
    {body : BodyMark p} {after : RootMark p} {packet : Packet regs}
    (preDone : finished semantics (preheader p) input PUnit.unit pre = some preBank)
    (reaches : ReflTransGen (BodyFire p old) (pending semantics (thetaBody p)) body)
    (bodyDone : finished semantics (thetaBody p) old PUnit.unit body = some packet)
    (step : RootFire p input (atBody p pre old body) after) :
    after = afterLatch p pre (feedback packet) (nextBankOf packet) := by
  have ready := Option.isSome_iff_exists.mpr ⟨_, bodyDone⟩
  have result := (completed_activation p old reaches ready).2
  have packetEq := Option.some.inj (bodyDone.symm.trans result)
  have consumed := (latch_step p old input (Option.isSome_iff_exists.mpr ⟨_, preDone⟩) reaches ready step).1
  rw [packetEq]
  cases guard : ((nextBank p model old).get p.again).down with
  | false => exact consumed.trans (congrArg (fun b => afterLatch p pre b _) guard)
  | true => exact consumed.trans (congrArg (fun b => afterLatch p pre b _) guard)

private theorem slice_complete {pre : PreMark p} {preBank old : Bank (regs := regs) model}
    (preDone : finished semantics (preheader p) input PUnit.unit pre = some preBank)
    (body : BodyMark p) (roots : List (RootMark p))
    (reaches : ReflTransGen (BodyFire p old) (pending semantics (thetaBody p)) body)
    (legal : List.IsChain (RootFire p input) (atBody p pre old body :: roots))
    (lastDone : (finished semantics (emitted p) input PUnit.unit
      (roots.getLastD (atBody p pre old body))).isSome) :
    (slice? p input pre old body roots).isSome := by
  induction roots generalizing body with
  | nil => exact False.elim (waiting_not_finished p input pre old body preDone lastDone)
  | cons after rest ih =>
    obtain ⟨fires, later⟩ := List.isChain_cons_cons.mp legal
    simp only [List.getLastD_cons] at lastDone
    simp only [slice?]
    split
    · rename_i packet ready
      have dest := completed_latch p input preDone reaches ready fires
      obtain ⟨proof, checked⟩ := Option.isSome_iff_exists.mp (checkFire_complete semantics colourEq fires)
      simp [checked, dest]
    · rename_i unfinished
      obtain ⟨child, inside, shape⟩ := advance p input preDone unfinished fires
      subst after
      obtain ⟨proof, checked⟩ := Option.isSome_iff_exists.mp (checkFire_complete semantics colourEq inside)
      obtain ⟨segment, smaller⟩ := Option.isSome_iff_exists.mp (ih child (reaches.tail inside) later lastDone)
      unfold atBody
      rw [(entryCut p).rest_attach]
      simp [checked, smaller]

theorem recover_complete {pre : PreMark p} {preBank : Bank (regs := regs) model}
    (preDone : finished semantics (preheader p) input PUnit.unit pre = some preBank)
    (fuel : Nat) (old : Bank (regs := regs) model) (roots : List (RootMark p))
    (fits : roots.length ≤ fuel)
    (legal : List.IsChain (RootFire p input) (atBody p pre old (pending semantics (thetaBody p)) :: roots))
    (lastDone : (finished semantics (emitted p) input PUnit.unit
      (roots.getLastD (atBody p pre old (pending semantics (thetaBody p))))).isSome) :
    (recover? p input pre fuel old roots).isSome := by
  induction fuel generalizing old roots with
  | zero =>
    have empty : roots = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero fits)
    subst roots
    exact False.elim (waiting_not_finished p input pre old _ preDone lastDone)
  | succ fuel ih =>
    obtain ⟨slice, cut⟩ := Option.isSome_iff_exists.mp (slice_complete p input preDone _ roots .refl legal lastDone)
    have suffix : List.IsChain (RootFire p input) (slice.after :: slice.remaining) := by
      apply List.IsChain.right_of_append (l₁ := atBody p pre old (pending semantics (thetaBody p)) ::
        slice.body.map (atBody p pre old))
      rw [List.cons_append, ← slice.split]
      exact legal
    have last : roots.getLastD (atBody p pre old (pending semantics (thetaBody p))) =
        slice.remaining.getLastD slice.after :=
      (congrArg (fun (marks : List (RootMark p)) => marks.getLastD (atBody p pre old (pending semantics (thetaBody p)))) slice.split).trans (last_after_append _ _ _ _)
    have length : roots.length = slice.body.length + (slice.remaining.length + 1) := by
      simpa using congrArg List.length slice.split
    rw [last] at lastDone
    simp only [recover?, cut, bind, Option.bind]
    split
    · rename_i missing
      have read := slice.firstOuter_eq p input
      rw [read] at missing
      cases missing
    · rename_i found read
      by_cases feedbackBit : feedback slice.packet = true
      · have nextMark : slice.after = atBody p pre (nextBankOf slice.packet) (pending semantics (thetaBody p)) := by
          rw [slice.destination, feedbackBit]
          rfl
        obtain ⟨result, subsequent⟩ := Option.isSome_iff_exists.mp
          (ih (nextBankOf slice.packet) slice.remaining (by omega) (nextMark ▸ suffix) (nextMark ▸ lastDone))
        simp [feedbackBit, subsequent]
      · have stopBit : feedback slice.packet = false := Bool.eq_false_iff.mpr feedbackBit
        have empty : slice.remaining = [] := by
          cases rest : slice.remaining with
          | nil => rfl
          | cons after rest =>
            rw [rest] at suffix
            have step := (List.isChain_cons_cons.mp suffix).1
            rw [slice.destination, stopBit] at step
            exact False.elim (committed_no_step p input preDone (nextBankOf slice.packet) step)
        have finalMark : (finished semantics (emitted p) input PUnit.unit slice.after).isSome := by
          rw [empty] at lastDone
          exact lastDone
        rw [dite_eq_right feedbackBit, dite_eq_left empty]
        split
        · simp
        · rename_i missing
          rw [missing] at finalMark
          cases finalMark

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Proofs
