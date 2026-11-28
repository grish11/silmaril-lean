module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg PortTy)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Operands Code)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.MLIR (sourceInputs)
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (Scope lowerCode_eval)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp opcode_eval)
open Silmaril.SSA.RVSDG (Tuple Locals Origin extend)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {scope : List Reg} {bank tests captures live : Nat} {fn : Func Reg}

private theorem checkTerm_sound {slot : Fin (tests + 1)} {term : Term Reg} {row : Row scope bank tests}
    (admitted : checkTerm scope bank slot term = some row) :
    row.term = term := by
  cases term with
  | jump target regs =>
    simp only [checkTerm] at admitted
    split at admitted
    · rename_i good
      obtain ⟨packet, checked, rfl⟩ := Option.map_eq_some_iff.mp admitted
      simp only [Row.term, Phi.checkPacket_registers checked, good.1]
    · cases admitted
  | cond selector target regs next tail =>
    simp only [checkTerm] at admitted
    split at admitted
    · split at admitted
      · rename_i good
        split at admitted
        · rename_i found
          obtain ⟨packet, checked, rfl⟩ := Option.map_eq_some_iff.mp admitted
          rcases good with ⟨rfl, rfl, rfl⟩
          simp only [Row.term, Phi.checkPacket_registers checked]
          congr 1
          exact List.getElem_idxOf (List.idxOf_lt_length_of_mem found)
        · cases admitted
      · cases admitted
    · cases admitted
  | ret => cases admitted
  | trap => cases admitted

theorem row_roundTrip (plan : Plan fn scope bank tests) (slot : Fin (tests + 1)) :
    fn.block? (occurrence slot).1 = some ⟨[], [], (plan.row slot).term⟩ := by
  have admitted : readRow fn scope bank slot = some (plan.row slot) :=
    (Option.some_get (plan.present slot)).symm
  cases found : fn.block? (occurrence slot).1 with
  | none => simp [readRow, found] at admitted
  | some block =>
    obtain ⟨params, ops, term⟩ := block
    cases params with
    | cons => simp [readRow, found] at admitted
    | nil =>
      cases ops with
      | cons => simp [readRow, found] at admitted
      | nil =>
        have checked : checkTerm scope bank slot term = some (plan.row slot) := by
          simpa [readRow, found] using admitted
        rw [checkTerm_sound checked]

theorem column_eq_phi (plan : Plan fn scope bank tests) (view : Phi.Checked fn tests)
    (slot : Fin (tests + 1)) :
    view.reemit slot.succ = some (1, (plan.row slot).column.registers) := by
  rw [← Phi.reemit_roundTrip view slot.succ]
  change (fn.block? (occurrence slot).1).bind (fun block => block.term.args[0]?) = _
  rw [row_roundTrip plan slot]
  cases plan.row slot <;> rfl

private theorem wordList_length {k : Nat} (values : Env (wordsTy k)) :
    (wordList values).length = k := by
  induction k with
  | zero => cases values; rfl
  | succ k ih => cases values with | cons _ rest => simp [wordList, ih rest]

theorem column_reads {Γ : List Width} {n : Nat} (width : scope.length = live)
    (env : Env (wordsTy live ++ Γ)) (frame : Frame Reg)
    (matched : Snapshot width env frame) (column : Phi.Packet scope n) :
    frame.readAll column.registers =
      some (wordList ((project (fun i => argAt live (i.cast width)) column).eval env)) := by
  induction column with
  | nil => rfl
  | cons i rest ih =>
    apply readAll_cons_eq_some.mpr
    exact ⟨_, _, matched i, ih, rfl⟩

private theorem project_there {Γ : List Width} {w : Width} {n : Nat}
    (resolve : Fin scope.length → Var Γ i64) (column : Phi.Packet scope n)
    (env : Env Γ) (value : BitVec w.val) :
    (project (fun i => .there (resolve i)) column).eval (.cons value env) =
      (project resolve column).eval env := by
  induction column with
  | nil => rfl
  | cons _ _ ih => simp only [project, Operands.eval, Env.get, ih]

private theorem forward_there {Γ : List Width} {w : Width} (n : Nat)
    (resolve : Fin n → Var Γ i64) (env : Env Γ) (value : BitVec w.val) :
    (forward n (fun i => .there (resolve i))).eval (.cons value env) = (forward n resolve).eval env := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [forward, Operands.eval, Env.get, ih]

private theorem forward_eval {Γ : List Width} (n : Nat) (packet : Env (wordsTy n)) (input : Env Γ) :
    (forward n (argAt n)).eval (packet.append input) = packet := by
  induction n with
  | zero => cases packet; rfl
  | succ n ih =>
    cases packet with
    | cons word packet =>
      change Env.cons word ((forward n (fun i => .there (argAt n i))).eval
        (.cons word (packet.append input))) = _
      rw [forward_there, ih packet]

private theorem nonzero_bit (x : Word) :
    (BitVec.ofBool ((0 : Word).ult x)).getLsbD 0 = decide (x ≠ 0) := by
  by_cases zero : x = 0#64
  · simp [zero, BitVec.ult]
  · simpa [BitVec.ult, BitVec.toNat_pos_of_ne_zero zero] using zero

private theorem test_eval (width : scope.length = live) (selector : Fin scope.length)
    (column : Phi.Packet scope bank) (next : Fin (tests + 1))
    (packet : Env (wordsTy live)) (input : Env (wordsTy captures)) :
    let env := packet.append input
    let value := fun i : Fin scope.length => argAt live (i.cast width)
    (dispatcher live width (.test selector column next)).eval evalOp (fun term env => term.eval env) env =
      .inl (if env.get (value selector) = 0 then ⟨.dispatch next, packet⟩
        else ⟨.header, (project value column).eval env⟩) := by
  dsimp only
  let env := packet.append input
  let value := fun i : Fin scope.length => argAt (Γ := wordsTy captures) live (i.cast width)
  let bit : BitVec Silmaril.MLIR.Pure.i1.val := BitVec.ofBool ((0 : Word).ult (env.get (value selector)))
  change @Sum.inl (Silmaril.MLIR.CF.Frame (Label live bank tests)) (Env [i64]) (if bit.getLsbD 0 then
      ⟨Label.header, (project (fun i => .there (.there (value i))) column).eval (.cons (w := Silmaril.MLIR.Pure.i1) bit (.cons (w := i64) 0 env))⟩
    else ⟨Label.dispatch next, (forward live (fun i => .there (.there (argAt live i)))).eval
      (.cons (w := Silmaril.MLIR.Pure.i1) bit (.cons (w := i64) 0 env))⟩) = _
  rw [project_there, project_there, forward_there, forward_there, forward_eval]
  have test : bit.getLsbD 0 = decide (env.get (value selector) ≠ 0) := nonzero_bit _
  rw [test]
  by_cases guard : env.get (value selector) = 0 <;> simp [guard, env, value]

theorem dispatcher_step {prog : Prog Reg} (found : prog.func? 0 = some fn) (wf : fn.WellFormed)
    {target : Silmaril.Machine.RTL.SSA.Block Reg} (headerFound : fn.block? 1 = some target)
    (arity : target.params.length = bank) (plan : Plan fn scope bank tests)
    (width : scope.length = live) (slot : Fin (tests + 1))
    (packet : Env (wordsTy live)) (input : Env (wordsTy captures)) (frame : Frame Reg) (mem : Memory)
    (matched : Snapshot width (packet.append input) frame) :
    StepAgreement (bank := bank) prog slot frame mem packet
      ((dispatcher live width (plan.row slot)).eval evalOp (fun term env => term.eval env) (packet.append input)) := by
  have block_at (label : Nat) : prog.block? 0 label = fn.block? label := by
    simp [Prog.block?, found]
  have atSource := (block_at (occurrence slot).1).trans (row_roundTrip plan slot)
  have atTarget := (block_at 1).trans headerFound
  have fetched : prog.fetch ⟨0, (occurrence slot).1, 0⟩ = some (.term (plan.row slot).term) :=
    Prog.fetch_term atSource
  let env := packet.append input
  let value := fun i : Fin scope.length => argAt (Γ := wordsTy captures) live (i.cast width)
  have ret (column : Phi.Packet scope bank) :
      ∃ latched, transfer prog ⟨⟨0, (occurrence slot).1, 0⟩, frame, [], mem⟩ 1 column.registers =
        .running ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
        latched.readAll target.params = some (wordList ((project value column).eval env)) := by
    have count : target.params.length = (wordList ((project value column).eval env)).length :=
      arity.trans (wordList_length _).symm
    obtain ⟨latched, wrote⟩ := writeAll_isSome frame count
    refine ⟨latched, ?_, readAll_writeAll wrote (params_nodup wf.singleAssignment headerFound)⟩
    simp [transfer, column_reads width env frame matched column, atTarget, wrote, value]
  cases row : plan.row slot with
  | last column =>
    rw [row] at atSource fetched
    obtain ⟨latched, moved, readback⟩ := ret column
    refine ⟨_, target, column.registers, latched, atSource, rfl,
      column_reads width env frame matched column, atTarget, ?_, readback⟩
    simpa only [step, fetched, Row.term] using moved
  | test selector column next =>
    rw [row] at atSource fetched
    rw [test_eval]
    dsimp only
    have read : frame.get scope[selector] = some (env.get (value selector)) := matched selector
    by_cases zero : env.get (value selector) = 0
    · have readZero : frame.get scope[selector] = some 0 := read.trans (congrArg some zero)
      have nextBlock := (block_at (occurrence next).1).trans (row_roundTrip plan next)
      have route : step prog ⟨⟨0, (occurrence slot).1, 0⟩, frame, [], mem⟩ =
          .running ⟨⟨0, (occurrence next).1, 0⟩, frame, [], mem⟩ := by
        simp only [step, fetched, Row.term, readZero, ite_true, transfer,
          show frame.readAll [] = some [] from rfl, nextBlock, Frame.writeAll]
      rw [ite_eq_left zero]
      exact ⟨rfl, _, atSource, rfl, route⟩
    · obtain ⟨latched, moved, readback⟩ := ret column
      rw [ite_eq_right zero]
      refine ⟨_, target, column.registers, latched, atSource, rfl,
        column_reads width env frame matched column, atTarget, ?_, readback⟩
      simpa only [step, fetched, Row.term, read, ite_eq_right zero] using moved

theorem liveOperands_eval {args : List (Diamond.Ty Width)} {past : List (List (Diamond.Ty Width))}
    {Δ : List Width} {names : Scope args past Δ} {env : Env Δ}
    {values : Tuple (Diamond.Val Silmaril.SSA.SeaOfNodes.MLIR.Word) args}
    {locals : Locals (Diamond.Val Silmaril.SSA.SeaOfNodes.MLIR.Word) past} (agree : names.Agrees env values locals)
    (wires : List (Origin args past (.value (.data i64)))) :
    (liveOperands names wires).eval env = readLive values locals wires := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    exact congrArg₂ Env.cons (agree.resolve wire) ih

variable {entrySigs sigs : List (List (Diamond.Ty Width))}

theorem header_frame (g : Program captures bank entrySigs sigs) (wires : Live captures bank sigs)
    (plan : Plan fn (liveRegs wires) bank tests)
    (input : Env (wordsTy captures)) (old : Loop.MLIR.CF.Bank.Values (wordsTy bank)) :
    let args := appendTuple old (sourceInputs input)
    let locals := g.header.eval Loop.MLIR.CF.model args PUnit.unit
    ((lower g wires plan).block .header).eval evalOp (fun term env => term.eval env)
      ((Loop.MLIR.CF.Bank.bankEnv old).append input) =
      .inl (if (Diamond.read Loop.MLIR.CF.model g.predicate args locals).down then
        ⟨.dispatch 0, readLive args locals wires⟩
      else ⟨.exit, .cons (Diamond.read Loop.MLIR.CF.model g.result args locals) .nil⟩) := by
  dsimp only
  refine lowerCode_eval Loop.MLIR.CF.opcode evalOp Loop.MLIR.CF.model.run opcode_eval
    g.header _ _ _ PUnit.unit (Loop.MLIR.CF.Bank.headerScope_agrees input old)
    (headerTerm g wires) (fun term env => term.eval env) _ ?_
  intro Δ scope env agree
  let args := appendTuple old (sourceInputs input)
  let locals := g.header.eval Loop.MLIR.CF.model args PUnit.unit
  have predicate : env.get (scope.resolveValue g.predicate) =
      BitVec.ofBool (Diamond.read Loop.MLIR.CF.model g.predicate args locals).down := agree.resolve g.predicate
  have result : env.get (scope.resolveValue g.result) = Diamond.read Loop.MLIR.CF.model g.result args locals :=
    agree.resolve g.result
  have operands := liveOperands_eval agree wires
  simp only [headerTerm, Silmaril.MLIR.CF.Terminator.eval, Silmaril.MLIR.CF.Edge.eval, operands, Operands.eval]
  erw [predicate, result]
  have testBit (b : Bool) : (BitVec.ofBool b).getLsbD 0 = b := by cases b <;> rfl
  erw [testBit]

variable {old new : Nat} {rtlEntry rtlHeader : List (List PortTy)}

theorem checked_dispatch_step (mapping : InputMap old new) (source : Source old old rtlEntry rtlHeader tests)
    {prog : Prog Reg} (accepted : Family.lowerChecked mapping source = some prog)
    (g : Program new old entrySigs sigs) (wires : Live new old sigs)
    (plan : Plan (lowerFunc (mapCaptures mapping source)) (liveRegs wires) old tests)
    (slot : Fin (tests + 1)) (packet : Env (wordsTy wires.length)) (input : Env (wordsTy new))
    (frame : Frame Reg) (mem : Memory)
    (matched : Snapshot (scope := liveRegs wires) (List.length_map ..) (packet.append input) frame) :
    StepAgreement (bank := old) prog slot frame mem packet
      (((lower g wires plan).block (.dispatch slot)).eval evalOp (fun term env => term.eval env)
        (packet.append input)) := by
  have em := (Family.lowerChecked_sound mapping source accepted).2.1
  have found : prog.func? 0 = some (lowerFunc (mapCaptures mapping source)) := by rw [em]; rfl
  have headerFound : (lowerFunc (mapCaptures mapping source)).block? 1 =
      some (Family.header (mapCaptures mapping source)) := rfl
  have arity : (Family.header (mapCaptures mapping source)).params.length = old := by
    simp [Family.header, Width.header, paramRegs]
  exact dispatcher_step found (Family.lowerFunc_wellFormed _) headerFound arity plan
    (List.length_map ..) slot packet input frame mem matched

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Proofs
