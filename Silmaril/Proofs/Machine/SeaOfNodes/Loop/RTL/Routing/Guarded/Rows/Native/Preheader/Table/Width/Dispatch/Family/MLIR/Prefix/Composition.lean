module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Thms

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame packValues)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.SSA.SeaOfNodes.MLIR (sourceInputs)
open Silmaril.SSA.PhiView (latch)

variable {old new tests : Nat} {rtlEntry rtlHeader : List (List PortTy)}
variable {entrySigs sigs : List (List (Diamond.Ty Width))}
variable {mapping : InputMap old new} {source : Family.Source old old rtlEntry rtlHeader tests}
variable {g : Program new old entrySigs sigs} {wires : Live new old sigs}
variable {sys : Setup mapping source g wires}

private theorem wordList_wordEnv {n : Nat} (value : WordTuple n) : wordList (wordEnv value) = words value := by
  induction n with
  | zero => cases value; rfl
  | succ n ih =>
    cases value with
    | cons x xs => exact congrArg (x :: ·) (ih xs)

private theorem wordList_inj {n : Nat} {x y : Env (wordsTy n)} (eq : wordList x = wordList y) :
    x = y := by
  induction n with
  | zero => cases x; cases y; rfl
  | succ n ih =>
    cases x with | cons a rest =>
    cases y with | cons b tail =>
    obtain ⟨rfl, h⟩ := List.cons.inj eq
    exact congrArg (Env.cons a) (ih h)

private theorem bankEnv_sourceInputs {Γ : List Width} (env : Env Γ) :
    Loop.MLIR.CF.Bank.bankEnv (sourceInputs env) = env := by
  induction env with
  | nil => rfl
  | cons x rest ih => exact congrArg (Env.cons x) ih

theorem predecessor_snapshot (sys : Setup mapping source g wires) (input : WordTuple new)
    {carried next : WordTuple old} {before ready after : Frame Reg} {mem : Memory}
    {slot : Fin (tests + 1)} {block : Block Reg}
    (alignment : HeaderMatch sys input carried)
    (cut : FeedbackCut (mapCaptures mapping source) sys.rtl input carried before ready after mem slot next block) :
    Snapshot (scope := liveRegs wires) (List.length_map ..)
      ((livePacket g wires input carried).append (wordEnv input)) ready := by
  intro i
  rw [← sys.register_eq i, cut.reads]
  exact congrArg some (alignment.2 i).symm

private theorem reached_label {x y : State Reg} (same : Result.running x = .running y) :
    x.point.label = y.point.label := congrArg (fun s => s.point.label) (Result.running.inj same)

private theorem selected_cf (sys : Setup mapping source g wires) (input : WordTuple new)
    {carried next : WordTuple old} {before ready after : Frame Reg} {mem : Memory}
    {slot : Fin (tests + 1)} {block : Block Reg}
    (cut : FeedbackCut (mapCaptures mapping source) sys.rtl input carried before ready after mem slot next block)
    {packet : Env (wordsTy wires.length)}
    (matched : Snapshot (scope := liveRegs wires) (List.length_map ..) (packet.append (wordEnv input)) ready) :
    (sys.cf.block (.dispatch slot)).eval evalOp (fun term env => term.eval env) (packet.append (wordEnv input)) =
      .inl (headerFrame wires.length tests next) := by
  have sim := MLIR.checked_dispatch_step mapping source sys.accepted g wires sys.plan slot
    packet (wordEnv input) ready mem matched
  change StepAgreement (bank := old) sys.rtl slot ready mem packet
    ((sys.cf.block (.dispatch slot)).eval evalOp (fun term env => term.eval env)
      (packet.append (wordEnv input))) at sim
  generalize (sys.cf.block (.dispatch slot)).eval evalOp (fun term env => term.eval env)
    (packet.append (wordEnv input)) = result at sim ⊢
  cases result with
  | inr _ => exact sim.elim
  | inl frame =>
    cases frame with
    | mk label args =>
      cases label with
      | exit => exact sim.elim
      | header =>
        obtain ⟨actual, target, regs, latched, found, operand, oldReads, _, _, _⟩ := sim
        have same : actual = block := Option.some.inj (found.symm.trans cut.found)
        subst actual
        have column : regs = emitColumn ((mapCaptures mapping source).rows.column slot) :=
          congrArg Prod.snd (Option.some.inj (operand.symm.trans cut.operand))
        rw [column, cut.packet] at oldReads
        have equal := (Option.some.inj oldReads).symm
        rw [← wordList_wordEnv next] at equal
        rw [wordList_inj equal]
      | dispatch next =>
        obtain ⟨_, _, _, _, machine⟩ := sim
        have impossible := reached_label (cut.feedback.symm.trans machine)
        change 1 = 3 + next.val at impossible
        omega

private theorem skipped_cf (sys : Setup mapping source g wires) (input : WordTuple new)
    {carried next : WordTuple old} {before ready after : Frame Reg} {mem : Memory}
    {slot : Fin (tests + 1)} {block : Block Reg}
    (cut : FeedbackCut (mapCaptures mapping source) sys.rtl input carried before ready after mem slot next block)
    {packet : Env (wordsTy wires.length)}
    (matched : Snapshot (scope := liveRegs wires) (List.length_map ..) (packet.append (wordEnv input)) ready)
    (current : Fin (tests + 1)) (inside : current.val < slot.val) :
    (sys.cf.block (.dispatch current)).eval evalOp (fun term env => term.eval env) (packet.append (wordEnv input)) =
      .inl (dispatchFrame old ⟨current.val + 1, by omega⟩ packet) := by
  have skipped := cut.fallthrough current.val inside
  have sim := MLIR.checked_dispatch_step mapping source sys.accepted g wires sys.plan current
    packet (wordEnv input) ready mem matched
  change StepAgreement (bank := old) sys.rtl current ready mem packet
    ((sys.cf.block (.dispatch current)).eval evalOp (fun term env => term.eval env)
      (packet.append (wordEnv input))) at sim
  generalize (sys.cf.block (.dispatch current)).eval evalOp (fun term env => term.eval env)
    (packet.append (wordEnv input)) = result at sim ⊢
  cases result with
  | inr _ => exact sim.elim
  | inl frame =>
    cases frame with
    | mk label args =>
      cases label with
      | exit => exact sim.elim
      | header =>
        obtain ⟨_, _, _, _, _, _, _, _, machine, _⟩ := sim
        have impossible := reached_label (machine.symm.trans skipped)
        change 1 = 3 + current.val + 1 at impossible
        omega
      | dispatch next =>
        obtain ⟨rfl, _, _, _, machine⟩ := sim
        have label := reached_label (machine.symm.trans skipped)
        have nextEq : next = ⟨current.val + 1, by omega⟩ := by
          apply Fin.ext
          change 3 + next.val = 3 + current.val + 1 at label
          change next.val = current.val + 1
          omega
        rw [nextEq]

private theorem dispatch_to_header (sys : Setup mapping source g wires) (input : WordTuple new)
    {carried next : WordTuple old} {before ready after : Frame Reg} {mem : Memory}
    {slot : Fin (tests + 1)} {block : Block Reg}
    (cut : FeedbackCut (mapCaptures mapping source) sys.rtl input carried before ready after mem slot next block)
    {packet : Env (wordsTy wires.length)}
    (matched : Snapshot (scope := liveRegs wires) (List.length_map ..) (packet.append (wordEnv input)) ready)
    (remaining : Nat) (current : Fin (tests + 1)) (ordered : current.val + remaining = slot.val) :
    Transfers sys.cf (wordEnv input) (remaining + 1) (dispatchFrame old current packet)
      (headerFrame wires.length tests next) := by
  induction remaining generalizing current with
  | zero =>
    have same : current = slot := Fin.ext (by simpa using ordered)
    subst current
    exact .next (selected_cf sys input cut matched) (.refl _)
  | succ remaining ih =>
    have inside : current.val < slot.val := by omega
    exact .next (skipped_cf sys input cut matched current inside)
      (ih ⟨current.val + 1, by omega⟩ (by simp; omega))

private theorem cut_phi (sys : Setup mapping source g wires) (input : WordTuple new)
    {carried next : WordTuple old} {before ready after : Frame Reg} {mem : Memory}
    {slot : Fin (tests + 1)} {block : Block Reg}
    (cut : FeedbackCut (mapCaptures mapping source) sys.rtl input carried before ready after mem slot next block) :
    latch sys.phi.view (sys.phi.edge slot.succ) (Phi.snapshot (lowerFunc (mapCaptures mapping source)).allDefs ready) =
      packValues (words next) := by
  obtain ⟨actual, atBlock, atOperand⟩ := Phi.readColumn_roundTrip sys.phi slot.succ
  have found := cut.found
  rw [(Family.lowerChecked_sound mapping source sys.accepted).2.1] at found
  have same : actual = block := Option.some.inj (atBlock.symm.trans found)
  subst actual
  have regs : (sys.phi.column slot.succ).registers = emitColumn ((mapCaptures mapping source).rows.column slot) :=
    congrArg Prod.snd (Option.some.inj (atOperand.symm.trans cut.operand))
  apply Phi.latch_agrees
  rw [regs]
  exact cut.packet

theorem visit_correct (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Memory)
    {carried next : WordTuple old} {slot : Fin (tests + 1)} (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input)) (aligned : HeaderMatch sys input carried)
    (taken : source.step (mapping.pull input) carried = .inr (slot, next)) :
    ∃ after, Visit sys input mem slot carried next before after := by
  obtain ⟨ready, after, block, cut⟩ :=
    Family.checked_feedback_cut mapping source sys.accepted input carried before mem matched slot next taken
  have snapshot := predecessor_snapshot sys input aligned cut
  have cfHeader := MLIR.header_frame g wires sys.plan (wordEnv input) (sourceInputs (wordEnv carried))
  rw [bankEnv_sourceInputs] at cfHeader
  have guard := aligned.1.trans cut.continuing
  dsimp only at cfHeader
  rw [guard] at cfHeader
  have enters : (sys.cf.block (.header)).eval evalOp (fun term env => term.eval env)
      ((wordEnv carried).append (wordEnv input)) = .inl (dispatchFrame old 0 (livePacket g wires input carried)) :=
    cfHeader
  refine ⟨after, cut.path, .next enters ?_, ready, block, cut, snapshot, cut_phi sys input cut⟩
  exact dispatch_to_header sys input cut snapshot slot.val 0 (by simp)

theorem prefix_correct (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {carried finish : WordTuple old}
    (admitted : Admitted sys input slots carried finish) (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input)) :
    ∃ after, Realized sys input mem slots carried before finish after := by
  induction admitted generalizing before with
  | stop _ => exact ⟨before, .stop matched⟩
  | visit aligned taken rest ih =>
    obtain ⟨middle, cut⟩ := visit_correct sys input mem before matched aligned taken
    obtain ⟨_, _, actual, _, _⟩ := cut.cut
    obtain ⟨after, suffix⟩ := ih middle actual.rebound
    exact ⟨after, .visit cut suffix⟩

private theorem transfers_run {start finish : Silmaril.MLIR.CF.Frame (Label wires.length old tests)}
    {input : Env (wordsTy new)} {count : Nat} (path : Transfers sys.cf input count start finish)
    (fuel : Nat) :
    sys.cf.runFrom evalOp (count + fuel) input start = sys.cf.runFrom evalOp fuel input finish := by
  induction path with
  | refl _ => rw [Nat.zero_add]
  | @next start middle finish count taken rest ih =>
    rw [show count + 1 + fuel = (count + fuel) + 1 by omega]
    unfold Silmaril.MLIR.CF.Cfg.runFrom
    rw [Silmaril.MLIR.CF.Cfg.runBlock, taken]
    exact ih

theorem realized_run (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Memory)
    {slots : List (Fin (tests + 1))} {carried finish : WordTuple old} {before after : Frame Reg}
    (path : Realized sys input mem slots carried before finish after) (rtlBudget cfBudget : Nat) :
    run sys.rtl (rtlCost rtlHeader.length slots + rtlBudget) ⟨⟨0, 1, 0⟩, before, [], mem⟩ =
      run sys.rtl rtlBudget ⟨⟨0, 1, 0⟩, after, [], mem⟩ ∧
    sys.cf.runFrom evalOp (cfCost slots + cfBudget) (wordEnv input) (headerFrame _ _ carried) =
      sys.cf.runFrom evalOp cfBudget (wordEnv input) (headerFrame _ _ finish) ∧
    ArgsMatch after (appendTuple finish input) := by
  induction path with
  | stop matched => exact ⟨by simp [rtlCost], by simp [cfCost], matched⟩
  | visit taken rest ih =>
    obtain ⟨rtl, cf, matched⟩ := ih
    refine ⟨?_, ?_, matched⟩
    · simp only [rtlCost, List.map_cons, List.sum_cons] at rtl ⊢
      rw [Nat.add_assoc]
      exact (run_through_prefix taken.rtlPath _).trans rtl
    · simp only [cfCost, List.map_cons, List.sum_cons] at cf ⊢
      rw [Nat.add_assoc]
      exact (transfers_run taken.cfPath _).trans cf

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Proofs
