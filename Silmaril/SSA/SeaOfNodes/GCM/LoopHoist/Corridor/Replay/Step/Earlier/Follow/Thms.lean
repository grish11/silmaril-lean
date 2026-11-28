module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Terminator)
open AfterReorder.Second (Candidate checkPrefixCut findCaptured?)
open Loop.MLIR.CF (Program evalOp model)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Step.State Input saved carried result extra} {first second : Nomination}
variable {prior : Earlier.Emission Input saved carried result extra} {moved : Emission prior}

/-- A successful earlier splice is also a valid starting state for finite replay. -/
theorem toLayout_invariant (firstDone : Earlier.emit? state first = some prior) :
    Layout.Invariant (toLayout prior) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.toLayout_invariant firstDone

/-- The physical scope contains exactly one definition per logical save. -/
theorem savedCount_eq (firstDone : Earlier.emit? state first = some prior) :
    savedCount prior = ((CurrentExtra prior) ++ [saved]).length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.savedCount_eq firstDone

/-- An accepted placement splices the remapped operands into the exact physical prefix. -/
theorem emit?_spec (accepted : emit? prior second = some moved) :
    Step.emit prior.append.next { second with cut := ((CurrentExtra prior) ++ [saved]).length } = .ok moved.append ∧
    checkPrefixCut prior.cfg (atLayout prior moved.append.candidate) second.cut = true ∧
    prior.splice.leading.insert? moved.append.candidate.op (savedCount prior - second.cut)
      (physicalOperands prior moved.append.candidate) = some moved.splice :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_spec accepted

/-- The surviving source identity, current typed binding, physical cut and
    actual ordinary and Φ uses agree with the checked emission. -/
theorem emit?_placement (accepted : emit? prior second = some moved) :
    prior.append.next.origins[moved.append.index]? = some second.origin ∧
    findCaptured? moved.append.index 0 (Saved.origins ((CurrentExtra prior) ++ [saved]))
      (prior.cfg.block .header) = some moved.append.candidate ∧
    Legal prior.cfg (atLayout prior moved.append.candidate).operands moved.append.candidate.uses ⟨none, second.cut⟩ ∧
    moved.splice.inserted.index = savedCount prior - second.cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_placement accepted

/-- The reference CFG is exactly the checked two-step append replay. -/
theorem emit?_append_replay (firstDone : Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (position : Nat) :
    Step.run state position [{ first with cut := (extra ++ [saved]).length },
      { second with cut := ((CurrentExtra prior) ++ [saved]).length }] = .ok ⟨_, moved.append.next⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_append_replay firstDone accepted position

/-- Remapped operands read the logical values of the actual reference prefix. -/
theorem physicalOperands_eval (firstDone : Earlier.emit? state first = some prior) (input : Env Input) :
    ∃ leading tail,
      Saved.splitPrefix? prior.append.next.cfg.entry ((CurrentExtra prior) ++ [saved]) = some (leading, tail) ∧
      ∀ candidate : Candidate Input saved carried result (CurrentExtra prior),
        (physicalOperands prior candidate).eval (prior.splice.leading.eval input) =
          candidate.inputs.eval (leading.eval input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.physicalOperands_eval firstDone input

theorem emit?_entry_targets (firstDone : Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) :
    (shape moved.cfg none).target = (shape moved.append.next.cfg none).target :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_entry_targets firstDone accepted

theorem Emission.block_eq (moved : Emission prior) :
    ∀ {args} (label : Label saved carried result (moved.append.candidate.width :: CurrentExtra prior) args),
      moved.cfg.block label = moved.append.next.cfg.block label := fun _ => rfl

/-- The final entry computes exactly the same logical transfer as two appends. -/
theorem emit?_entry_eq (firstDone : Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) :
    moved.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      moved.append.next.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_entry_eq firstDone accepted input

/-- Each actual move prepends its value to entry and feedback while
    preserving the previous packet and exact exit payload. -/
theorem emit?_routes (firstDone : Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.cfg.entry input values) :
    let firstValue := evalOp prior.append.candidate.op (prior.append.candidate.inputs.eval (values.append input))
    let nextValues := Env.cons firstValue values
    let nextValue := evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (nextValues.append input))
    Saved.StepRoutes state.cfg prior.cfg input values firstValue ∧
      Saved.StepRoutes prior.cfg moved.cfg input nextValues nextValue :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_routes firstDone accepted matched

theorem emit?_run_eq (firstDone : Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = moved.append.next.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_run_eq firstDone accepted input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem emit?_denotePart (firstDone : Earlier.emit? state first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) :
    (Cfg.embed moved.cfg).denotePart evalOp input =
      (Cfg.embed moved.append.next.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_denotePart firstDone accepted input

theorem emit?_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {prior : Earlier.Emission Input two.prepared.intermediate.1 carried result [two.prepared.consumer.width]}
    {moved : Emission prior}
    (seed : replay g header [producer, consumer] = .ok (.two record consumer two))
    (firstDone : Earlier.emit? (Step.fromTwo record consumer two) first = some prior)
    (accepted : emit? prior second = some moved) (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.emit?_fromTwo_budget seed firstDone
    accepted input budget

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow
