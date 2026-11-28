module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
  (withHeader withHeader_frames withHeader_run_eq withHeader_denotePart)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair
open Loop.MLIR.CF (Program TargetOp evalOp lower model lower_run)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {cfg middle out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {request first second : Request}

theorem move?_checked (moved : move? cfg request = some out) :
    Header.Later.checkBindingCut cfg request.binding request.point = true := by
  by_cases earlier : request.insertion < request.binding
  · by_cases checked : Header.Later.checkBindingCut cfg request.binding request.point = true
    · exact checked
    · simp [move?, earlier, checked] at moved
  · exact Header.Later.moveCfgAt?_checked (by simpa [move?, earlier] using moved)

theorem move?_header (moved : move? cfg request = some out) :
    ∃ header, out = withHeader cfg header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        (cfg.block .header).eval evalOp (fun term vals => term.eval vals) env := by
  by_cases earlier : request.insertion < request.binding
  · exact Header.Earlier.moveAt?_header (by simpa [move?, earlier, move?_checked moved] using moved)
  · exact Header.Later.moveCfgAt?_header (by simpa [move?, earlier] using moved)

theorem schedule?_steps (accepted : schedule? g first second = some out) :
    ∃ middle, move? (lower g) first = some middle ∧ second.binding ≠ first.insertion ∧
      move? middle second = some out := by
  obtain ⟨middle, firstMove, last⟩ := Option.bind_eq_some_iff.mp accepted
  by_cases repeated : second.binding = first.insertion
  · simp [repeated] at last
  · exact ⟨middle, firstMove, repeated, by simpa [repeated] using last⟩

/-- A rejected second request yields no rewritten CFG. -/
theorem schedule?_refuses_second (firstMove : move? (lower g) first = some middle)
    (secondRejected : move? middle second = none) : schedule? g first second = none := by
  simp [schedule?, firstMove, secondRejected]

private theorem schedule?_header (accepted : schedule? g first second = some out) :
    ∃ header, out = withHeader (lower g) header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        ((lower g).block .header).eval evalOp (fun term vals => term.eval vals) env := by
  obtain ⟨middle, firstMove, _, secondMove⟩ := schedule?_steps accepted
  obtain ⟨_, rfl, firstAgrees⟩ := move?_header firstMove
  obtain ⟨header, rfl, secondAgrees⟩ := move?_header secondMove
  exact ⟨header, rfl, fun env => (secondAgrees env).trans (firstAgrees env)⟩

theorem schedule?_frames (accepted : schedule? g first second = some out) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) := by
  obtain ⟨_, rfl, agrees⟩ := schedule?_header accepted
  exact withHeader_frames agrees input

theorem schedule?_run_eq (accepted : schedule? g first second = some out) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, rfl, agrees⟩ := schedule?_header accepted
  exact withHeader_run_eq agrees input fuel

theorem schedule?_budget (accepted : schedule? g first second = some out) (input : Env Input)
    (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (schedule?_run_eq accepted input _).trans (lower_run g input budget)

theorem schedule?_denotePart (accepted : schedule? g first second = some out) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input := by
  obtain ⟨_, rfl, agrees⟩ := schedule?_header accepted
  exact withHeader_denotePart agrees input

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair
