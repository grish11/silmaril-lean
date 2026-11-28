module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Defs

import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame Opcode packValues)
open Silmaril.Machine.RTL.SSA (run StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)
open Silmaril.Machine.RTL.SSA (toLambdaSSA)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
variable {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
variable {origins : List (HeaderWord new old sigs)}

/-- Certify the single zero successor of a reached header, including its exact exit register and the actual CF packet. -/
theorem taken (compiled : Compiled mapping source origins) (input : WordTuple new)
    (mem : Memory) (carried : WordTuple old) (before : Frame Reg) (value : Word)
    (matched : ArgsMatch before (appendTuple carried input))
    (exits : source.step (mapping.pull input) carried = .inl value) :
    Taken compiled input mem carried before value :=
  Proofs.taken compiled input mem carried before value matched exits

/-- Two CF blocks and the RTL producer count plus two instructions complete the taken exit. -/
theorem taken_runs {compiled : Compiled mapping source origins} {input : WordTuple new}
    {mem : Memory} {carried : WordTuple old} {before : Frame Reg} {value : Word}
    (exit : Taken compiled input mem carried before value) :
    run compiled.rtl (sigs.length + 2) ⟨⟨0, 1, 0⟩, before, [], mem⟩ = .returned [value] mem ∧
    compiled.setup.cf.runFrom evalOp 2 (wordEnv input) (headerFrame _ _ carried) = some (.cons value .nil) :=
  Proofs.taken_runs exit

/-- Compose the exact CF/RTL prefix costs and positional Φ latches with the first taken exit. -/
theorem after_prefix (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {carried finish : WordTuple old} (before : Frame Reg) (value : Word)
    (matched : ArgsMatch before (appendTuple carried input))
    (feedbacks : Feedbacks source (mapping.pull input) slots carried finish)
    (exits : source.step (mapping.pull input) finish = .inl value) :
    ∃ after, Realized compiled.setup input mem slots carried before finish after ∧
      Taken compiled input mem finish after value ∧
      run compiled.rtl (rtlCost sigs.length slots + (sigs.length + 2))
        ⟨⟨0, 1, 0⟩, before, [], mem⟩ = .returned [value] mem ∧
      compiled.setup.cf.runFrom evalOp (cfCost slots + 2) (wordEnv input) (headerFrame _ _ carried) =
        some (.cons value .nil) :=
  Proofs.after_prefix compiled input mem before value matched feedbacks exits

/-- A native return path determines the actual checked entry, positional
feedback latches, and first taken exit in both targets. -/
theorem from_return_path (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {value : Word}
    (path : source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value) :
    let initial := source.primary.initial model (mapping.pull input)
    ∃ before finish after,
      compiled.rtl.start 0 (words input) mem =
        some ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩ ∧
      StepsNWithin compiled.rtl [] (entrySigs.length + 1)
        ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩ ⟨⟨0, 1, 0⟩, before, [], mem⟩ ∧
      Realized compiled.setup input mem slots initial before finish after ∧
      Taken compiled input mem finish after value ∧
      compiled.rtl.runMain (entrySigs.length + 1 + (rtlCost sigs.length slots + (sigs.length + 2)))
        0 (words input) mem = .returned [value] mem ∧
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) :=
  Proofs.from_return_path compiled input mem path

/-- A native finite return from entry witnesses actual CF and RTL results and exit zero in the canonical typed λSSA translation. -/
theorem returns (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {value : Word}
    (path : source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value)
    (env : Env Word) (entry : env 0 = packValues (words input)) :
    compiled.rtl.runMain (entrySigs.length + 1 + (rtlCost sigs.length slots + (sigs.length + 2)))
      0 (words input) mem = .returned [value] mem ∧
    compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) ∧
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 (packValues [value]) mem :=
  Proofs.returns compiled input mem path env entry

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit
