module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame Opcode packValues)
open Silmaril.Machine.RTL.SSA (Prog run StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)
open Silmaril.Machine.RTL.SSA (toLambdaSSA run_returned)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
variable {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
variable {origins : List (HeaderWord new old sigs)}

theorem taken (compiled : Compiled mapping source origins) (input : WordTuple new)
    (mem : Memory) (carried : WordTuple old) (before : Frame Reg) (value : Word)
    (matched : ArgsMatch before (appendTuple carried input))
    (exits : source.step (mapping.pull input) carried = .inl value) :
    Taken compiled input mem carried before value := by
  obtain ⟨ready, cut⟩ :=
    Family.checked_exit_cut mapping source compiled.accepted input carried before mem matched value exits
  refine ⟨⟨ready, cut⟩, ?_, Producer.header_exit compiled input carried value cut, rfl⟩
  simp only [check, decide_eq_true_eq]
  exact ⟨rfl, rfl⟩

theorem taken_runs {compiled : Compiled mapping source origins} {input : WordTuple new}
    {mem : Memory} {carried : WordTuple old} {before : Frame Reg} {value : Word}
    (exit : Taken compiled input mem carried before value) :
    run compiled.rtl (sigs.length + 2) ⟨⟨0, 1, 0⟩, before, [], mem⟩ = .returned [value] mem ∧
    compiled.setup.cf.runFrom evalOp 2 (wordEnv input) (headerFrame _ _ carried) = some (.cons value .nil) := by
  obtain ⟨_, cut⟩ := exit.rtl
  constructor
  · rw [run_through_prefix cut.produced 2]
    simp only [run, cut.branch, cut.returned]
  · unfold Cfg.runFrom
    rw [Cfg.runBlock, exit.cfBranch]
    change compiled.setup.cf.runBlock evalOp (wordEnv input) 1 (compiled.setup.cf.block .exit)
      ((Silmaril.MLIR.Arith.Env.cons (w := Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF.i64) value .nil).append
        (wordEnv input)) = _
    rw [Cfg.runBlock, exit.cfReturn]

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
        some (.cons value .nil) := by
  obtain ⟨after, realized⟩ := Producer.prefix_correct compiled input mem feedbacks before matched
  obtain ⟨rtl, cf, reestablished⟩ := Prefix.realized_run _ input mem realized (sigs.length + 2) 2
  have exit := taken compiled input mem finish after value reestablished exits
  obtain ⟨rtlExit, cfExit⟩ := taken_runs exit
  exact ⟨after, realized, exit, rtl.trans rtlExit, cf.trans cfExit⟩

private theorem split_return {source : Family.Source old old entrySigs sigs tests}
    {input : WordTuple old} {slots : List (Fin (tests + 1))} {carried : WordTuple old} {value : Word}
    (path : source.ReturnsAlong input slots carried value) :
    ∃ finish, Feedbacks source input slots carried finish ∧ source.step input finish = .inl value := by
  induction path with
  | exit hit => exact ⟨_, .stop _, hit⟩
  | feedback hit _ ih =>
    obtain ⟨finish, feedbacks, exits⟩ := ih
    exact ⟨finish, .visit hit feedbacks, exits⟩

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
      compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) := by
  obtain ⟨finish, feedbacks, exits⟩ := split_return path
  obtain ⟨started, before, entered, matched⟩ := Family.entry_packet mapping source compiled.accepted input mem
  obtain ⟨after, realized, exit, rtl, cf⟩ := after_prefix compiled input mem before value matched feedbacks exits
  have machine := (run_through_prefix entered _).trans rtl
  refine ⟨before, finish, after, started, entered, realized, exit, ?_, ?_⟩
  · simpa only [Prog.runMain, started] using machine
  · unfold Cfg.run
    rw [Cfg.runBlock, Producer.entry_frame compiled input]
    exact cf

theorem returns (compiled : Compiled mapping source origins) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {value : Word}
    (path : source.ReturnsAlong (mapping.pull input) slots (source.primary.initial model (mapping.pull input)) value)
    (env : Env Word) (entry : env 0 = packValues (words input)) :
    compiled.rtl.runMain (entrySigs.length + 1 + (rtlCost sigs.length slots + (sigs.length + 2)))
      0 (words input) mem = .returned [value] mem ∧
    compiled.setup.cf.run evalOp (cfCost slots + 2 + 1) (wordEnv input) = some (.cons value .nil) ∧
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) compiled.rtl.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping source))) mem 0 (packValues [value]) mem := by
  obtain ⟨_, _, _, started, _, _, _, rtl, cf⟩ := from_return_path compiled input mem path
  have machine := rtl
  rw [Prog.runMain, started] at machine
  exact ⟨rtl, cf, (Phi.region_return_iff mapping source compiled.accepted input env entry mem mem [value]).mpr
    ⟨_, started, run_returned machine⟩⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Exit.Proofs
