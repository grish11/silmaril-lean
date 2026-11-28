module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Correctness

/-! # Finite returns and exact header transfers -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (CallOracle Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg entry model word)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)

namespace Profile

variable (p : Profile)

/-- The emitted function satisfies the machine SSA signature, single assignment,
dominance, and block argument checks for every admitted schedule. -/
theorem lower_wellFormed : p.lowerFunc.WellFormed :=
  Proofs.lower_wellFormed p

/-- Finite execution returns exactly the source's singleton word and
preserves the entire memory, for every seed and stride. -/
theorem lower_returns_iff (seed delta : Word) (initial final : Memory) (returned : List Word) :
    p.lower.oracle 0 [seed, delta] initial returned final ↔
      ∃ value : Word, p.graph.Returns model (entry seed delta) value ∧
        returned = [value] ∧ final = initial :=
  Proofs.lower_returns_iff p seed delta initial final returned

/-- An exact finite run with `n` source backedges takes `4 * n + 5`
running steps, followed by the terminal return step. -/
theorem lower_stepsN_iff (seed delta : Word) (initial final : Memory)
    (returned : List Word) (n : Nat) :
    (∃ start finish, p.lower.start 0 [seed, delta] initial = some start ∧
      StepsNWithin p.lower [] (4 * n + 5) start finish ∧
        step p.lower finish = .returned returned final) ↔
    ∃ value : Word, p.graph.ReturnsAfter model (entry seed delta) n
      (p.graph.initial model (entry seed delta)) value ∧ returned = [value] ∧ final = initial :=
  Proofs.lower_stepsN_iff p seed delta initial final returned n

/-- Entries and feedback remain two distinct source successor occurrences. -/
theorem incoming_operand (edge : Incoming) :
    ((p.lowerFunc.block? (incomingSlot edge).1).bind
      fun block => block.term.args[(incomingSlot edge).2]?) =
      some (1, [p.incomingRegister edge]) :=
  Proofs.incoming_operand p edge

theorem latch_feedback (seed delta old : Word) :
    let args := appendTuple (Tuple.cons (F := Val model.value) (t := .value word) old .nil) (entry seed delta)
    p.graph.latch model .backedge args (p.graph.header.eval model args PUnit.unit) =
      .cons (p.update.eval old delta) .nil :=
  Proofs.latch_feedback p seed delta old

/-- Executing the actual producer schedule updates exactly the three
results in the frame and leaves memory unchanged. -/
theorem header_exec_iff (oracle : CallOracle) (fr done : Frame Reg) (mem final : Memory)
    (old delta : Word) (hold : fr.get .phi = some old) (hdelta : fr.get (.arg 1) = some delta) :
    Ops.Exec oracle p.header.ops fr mem done final ↔
      done = p.headerFrame fr old delta ∧ final = mem :=
  Proofs.header_exec_iff p oracle fr done mem final old delta hold hdelta

/-- The typed native guard and machine test select the same projection. -/
theorem native_step (seed delta old : Word) :
    p.graph.step model (entry seed delta) (.cons old .nil) =
      if p.guardWord old delta = 0 then .inl old else .inr (.cons (p.update.eval old delta) .nil) :=
  Proofs.source_step p seed delta old

/-- Run the three emitted producers and the actual branch, preserving the
entire memory. The two successors have their original block arguments. -/
theorem header_activation (fr : Frame Reg) (mem : Memory) (old delta : Word)
    (hold : fr.get .phi = some old) (hdelta : fr.get (.arg 1) = some delta) :
    let after := p.headerFrame fr old delta
    StepsNWithin p.lower [] 4 ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (if p.guardWord old delta = 0 then ⟨⟨0, 2, 0⟩, after.set (.node 3) old, [], mem⟩
       else ⟨⟨0, 1, 0⟩, after.set .phi (p.update.eval old delta), [], mem⟩) :=
  Proofs.header_activation p fr mem old delta hold hdelta

/-- The actual backedge transfer latches the newly computed word. -/
theorem step_feedback (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory)
    (old delta : Word) (taken : p.guardWord old delta ≠ 0) :
    let after := p.headerFrame fr old delta
    step p.lower ⟨⟨0, 1, p.header.ops.length⟩, after, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, after.set .phi (p.update.eval old delta), stack, mem⟩ :=
  Proofs.step_feedback p fr stack mem old delta taken

end Profile

/-- The emitted function satisfies the machine SSA signature, definition,
dominance and block argument checks. -/
theorem lower_wellFormed : lowerFunc.WellFormed := by decide

/-- Machine execution returns exactly the source's singleton word and
preserves the entire memory, for all machine-word seeds and strides. -/
theorem lower_returns_iff (seed delta : Word) (initial final : Memory) (returned : List Word) :
    lower.oracle 0 [seed, delta] initial returned final ↔
      ∃ value : Word, graph.Returns model (entry seed delta) value ∧
        returned = [value] ∧ final = initial :=
  Proofs.lower_returns_iff countdown seed delta initial final returned

/-- The actual terminator operand of each source occurrence enters the same
header parameter. The two occurrences are indexed by source label and ordinal. -/
theorem incoming_operand (edge : Incoming) :
    ((lowerFunc.block? (incomingSlot edge).1).bind
      fun block => block.term.args[(incomingSlot edge).2]?) =
      some (1, [incomingRegister edge]) :=
  Proofs.incoming_operand countdown edge

theorem latch_entry (seed delta : Word) :
    graph.initial model (entry seed delta) = .cons seed .nil :=
  Proofs.latch_entry countdown seed delta

theorem latch_feedback (seed delta old : Word) :
    let args := appendTuple (Tuple.cons (F := Val model.value) (t := .value word) old .nil) (entry seed delta)
    graph.latch model .backedge args (graph.header.eval model args PUnit.unit) =
      .cons (old - delta) .nil :=
  Proofs.latch_feedback countdown seed delta old

/-- Transfer reads the actual incoming register before rebinding Phi. All
other registers, the stack and memory retain their pre-transfer state. -/
theorem transfer_incoming (edge : Incoming) (s : State Reg) (value : Word)
    (func : s.point.func = 0) (read : s.frame.get (incomingRegister edge) = some value) :
    transfer lower s 1 [incomingRegister edge] =
      .running ⟨⟨0, 1, 0⟩, s.frame.set .phi value, s.stack, s.mem⟩ :=
  Proofs.transfer_incoming countdown edge s value func read

/-- Executing the actual producer instructions updates exactly the three
results in the post-operation frame and leaves memory unchanged. -/
theorem header_exec_iff (oracle : CallOracle) (fr done : Frame Reg) (mem final : Memory)
    (old delta : Word) (hold : fr.get .phi = some old)
    (hdelta : fr.get (.arg 1) = some delta) :
    Ops.Exec oracle header.ops fr mem done final ↔
      done = headerFrame fr old delta ∧ final = mem :=
  Proofs.header_exec_iff countdown oracle fr done mem final old delta hold hdelta

/-- Executing the preheader's terminator binds the source entry latch. -/
theorem step_entry (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory)
    (seed : Word) (read : fr.get (.arg 0) = some seed) :
    step lower ⟨⟨0, 0, 0⟩, fr, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, fr.set .phi seed, stack, mem⟩ :=
  Proofs.step_entry countdown fr stack mem seed read

/-- A taken feedback branch binds the source backedge latch from the
producer frame, leaving the remainder of that frame untouched. -/
theorem step_feedback (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory)
    (old delta : Word) (taken : old - delta ≠ 0) :
    let after := headerFrame fr old delta
    step lower ⟨⟨0, 1, header.ops.length⟩, after, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, after.set .phi (old - delta), stack, mem⟩ :=
  Proofs.step_feedback countdown fr stack mem old delta (Proofs.countdown_guard_ne old delta taken)

end Silmaril.Machine.SeaOfNodes.Loop.RTL
