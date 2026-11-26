module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Terminator)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow
open AfterReorder.Second (checkPrefixCut findCaptured?)
open Loop.MLIR.CF (Program evalOp model lower_run)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Step.State Input saved carried result extra} {first second : Nomination}
variable {prior : Step.Earlier.Emission Input saved carried result extra} {moved : Emission prior}

theorem toLayout_invariant (firstDone : Step.Earlier.emit? state first = some prior) :
    Step.Layout.Invariant (toLayout prior) := by
  obtain ⟨_, _, _, _, _, splice⟩ := Step.Earlier.emit?_spec firstDone
  exact ⟨Saved.Prefix.insert?_length splice, Step.Earlier.emit?_prefix_agree firstDone,
    Step.Earlier.emit?_entry_targets firstDone, Step.Earlier.emit?_entry_eq firstDone⟩

theorem savedCount_eq (firstDone : Step.Earlier.emit? state first = some prior) :
    savedCount prior = ((CurrentExtra prior) ++ [saved]).length :=
  Step.Layout.savedCount_eq (toLayout_invariant firstDone)

private theorem emit?_toMove (accepted : emit? prior second = some moved) :
    Step.Layout.emit? (toLayout prior) second = some moved.toMove := by
  obtain ⟨⟨append, splice⟩, done, output⟩ := Option.map_eq_some_iff.mp accepted
  cases output
  exact done

theorem emit?_spec (accepted : emit? prior second = some moved) :
    Step.emit prior.append.next { second with cut := ((CurrentExtra prior) ++ [saved]).length } = .ok moved.append ∧
    checkPrefixCut prior.cfg (atLayout prior moved.append.candidate) second.cut = true ∧
    prior.splice.leading.insert? moved.append.candidate.op (savedCount prior - second.cut)
      (physicalOperands prior moved.append.candidate) = some moved.splice :=
  Step.Layout.emit?_spec (emit?_toMove accepted)

theorem emit?_placement (accepted : emit? prior second = some moved) :
    prior.append.next.origins[moved.append.index]? = some second.origin ∧
    findCaptured? moved.append.index 0 (Saved.origins ((CurrentExtra prior) ++ [saved]))
      (prior.cfg.block .header) = some moved.append.candidate ∧
    Legal prior.cfg (atLayout prior moved.append.candidate).operands moved.append.candidate.uses ⟨none, second.cut⟩ ∧
    moved.splice.inserted.index = savedCount prior - second.cut :=
  Step.Layout.emit?_placement (emit?_toMove accepted)

theorem emit?_append_replay (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (position : Nat) :
    Step.run state position [{ first with cut := (extra ++ [saved]).length },
      { second with cut := ((CurrentExtra prior) ++ [saved]).length }] = .ok ⟨_, moved.append.next⟩ := by
  simp only [Step.run, (Step.Earlier.emit?_spec firstDone).2.1, (emit?_spec accepted).1]

theorem physicalOperands_eval (firstDone : Step.Earlier.emit? state first = some prior) (input : Env Input) :
    ∃ leading tail,
      Saved.splitPrefix? prior.append.next.cfg.entry ((CurrentExtra prior) ++ [saved]) = some (leading, tail) ∧
      ∀ candidate : AfterReorder.Second.Candidate Input saved carried result (CurrentExtra prior),
        (physicalOperands prior candidate).eval (prior.splice.leading.eval input) =
          candidate.inputs.eval (leading.eval input) :=
  Step.Layout.physicalOperands_eval (toLayout_invariant firstDone) input

theorem emit?_entry_targets (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) :
    (shape moved.cfg none).target = (shape moved.append.next.cfg none).target :=
  (Step.Layout.emit?_invariant (toLayout_invariant firstDone) (emit?_toMove accepted)).targets

theorem emit?_entry_eq (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) :
    moved.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      moved.append.next.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input :=
  (Step.Layout.emit?_invariant (toLayout_invariant firstDone) (emit?_toMove accepted)).entry input

theorem emit?_routes (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.cfg.entry input values) :
    let firstValue := evalOp prior.append.candidate.op (prior.append.candidate.inputs.eval (values.append input))
    let nextValues := Env.cons firstValue values
    let nextValue := evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (nextValues.append input))
    Saved.StepRoutes state.cfg prior.cfg input values firstValue ∧
      Saved.StepRoutes prior.cfg moved.cfg input nextValues nextValue := by
  obtain ⟨_, _, foundFirst, _, emittedFirst, _, _⟩ := Step.emit_spec (Step.Earlier.emit?_spec firstDone).2.1
  have matchedAppend := (AfterReorder.Second.Emit.emitAt?_step matched foundFirst emittedFirst).2
  exact ⟨Step.Earlier.emit?_routes firstDone matched,
    Step.Layout.emit?_routes (toLayout_invariant firstDone) (emit?_toMove accepted) matchedAppend⟩

theorem emit?_run_eq (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = moved.append.next.cfg.run evalOp fuel input :=
  Step.Layout.state_run_eq (Step.Layout.emit?_invariant (toLayout_invariant firstDone) (emit?_toMove accepted)) input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem emit?_denotePart (firstDone : Step.Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) :
    (Cfg.embed moved.cfg).denotePart evalOp input =
      (Cfg.embed moved.append.next.cfg).denotePart evalOp input :=
  Step.Layout.state_denotePart (Step.Layout.emit?_invariant (toLayout_invariant firstDone) (emit?_toMove accepted)) input

theorem emit?_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {prior : Step.Earlier.Emission Input two.prepared.intermediate.1 carried result [two.prepared.consumer.width]}
    {moved : Emission prior}
    (seed : replay g header [producer, consumer] = .ok (.two record consumer two))
    (firstDone : Step.Earlier.emit? (Step.fromTwo record consumer two) first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) := by
  exact (emit?_run_eq firstDone accepted input _).trans
    ((Step.fromTwo_run_eq seed (emit?_append_replay firstDone accepted 2) input _).trans (lower_run g input budget))

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow
