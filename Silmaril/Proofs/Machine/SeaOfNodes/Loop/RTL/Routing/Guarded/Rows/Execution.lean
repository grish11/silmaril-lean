module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Execution

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWith emitOpWith model)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val read)
open Silmaril.SSA.SeaOfNodes.GVN
  (keepOrigin newest newestIndex read_keepOrigin read_newest)
open Silmaril.SSA.SeaOfNodes.Loop (Graph appendTuple)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)

private theorem read_joined {args : List PortTy} {past sigs tail : List (List PortTy)} {t : PortTy}
    (flow : Dataflow WordOp args past sigs) (rest : Dataflow WordOp args (extend past sigs) tail)
    (wire : Origin args (extend (extend past sigs) tail) t)
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) :
    read model (joinedOrigin (past := past) (sigs := sigs) (tail := tail) wire) entry ((appendFlow flow rest).eval model entry locals) =
      read model wire entry (rest.eval model entry (flow.eval model entry locals)) := by
  induction flow with
  | nil => rfl
  | cons op operands next ih => exact ih rest wire _

private theorem cast_register {args : List PortTy} {source target : List (List PortTy)} {t : PortTy}
    (same : source = target) (wire : Origin args source t) :
    register (same ▸ wire : Origin args target t).address = register wire.address := by
  cases same
  rfl

private theorem joined_register {args : List PortTy} {past sigs tail : List (List PortTy)} {t : PortTy}
    (wire : Origin args (extend (extend past sigs) tail) t) :
    register (joinedOrigin (past := past) (sigs := sigs) (tail := tail) wire).address = register wire.address :=
  cast_register (extend_append past sigs tail).symm wire

private theorem newest_register {args head : List PortTy} {past : List (List PortTy)} {t : PortTy}
    (port : Port head t) : register (newest (args := args) (past := past) port).address = .node past.length := by
  change Reg.node (newestIndex head past).val = _
  congr 1
  induction past with
  | nil => rfl
  | cons h tail ih =>
    change (newestIndex head tail).val + 1 = tail.length + 1
    rw [ih]

private theorem row_word_reads {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) (wire : Origin (bankArgs arity) p.rowPast wordPort) :
    (p.rowFrame fr old).get (register wire.address) =
      some (read model wire (appendTuple old input) (p.row.eval model (appendTuple old input) PUnit.unit)) := by
  apply row_reads_at (argumentPort arity) p.updates [] input old fr PUnit.unit _ wire
  intro origin
  cases origin with
  | arg port => exact agree port
  | output i _ => exact i.elim0

private theorem row_producer_reads {arity : Nat} (p : Plan arity) (old : WordTuple arity)
    (fr : Frame Reg) (index : Fin p.updates.length) :
    (p.rowFrame fr old).get (register (p.producerWire index).address) =
      some (p.updates[index].evalAt (argumentPort arity) old) := by
  change (p.rowFrame fr old).get (.node index.val) = _
  simpa only [Nat.zero_add, Plan.rowFrame] using rowFrameAt_read (argumentPort arity) old p.updates 0 fr index

private theorem producer_read {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) (index : Fin p.updates.length) :
    read model (p.producerWire index) (appendTuple old input)
      (p.row.eval model (appendTuple old input) PUnit.unit) =
        p.updates[index].evalAt (argumentPort arity) old :=
  Option.some.inj ((row_word_reads p input old fr agree (p.producerWire index)).symm.trans
    (row_producer_reads p old fr index))

private theorem exit_read {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    read model p.exitWire (appendTuple old input)
      (p.row.eval model (appendTuple old input) PUnit.unit) = p.exitValue old := by
  cases selected : p.exitProducer with
  | none =>
    simp only [Plan.exitWire, Plan.exitValue, selected, Option.elim]
    exact suffix_get input old (argumentPort arity p.exitSlot)
  | some index =>
    simpa only [Plan.exitWire, Plan.exitValue, selected, Option.elim] using
      producer_read p input old fr agree index

private theorem setup_rhs_read {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input))
    (operand : GuardOperand arity p.updates.length) :
    let args := appendTuple old input
    let locals := p.row.eval model args PUnit.unit
    read model (guardRhsWire p.producerWire operand) args ((guardSetup p.limit operand).eval model args locals) =
      GuardOperand.eval p.updates p.limit old operand := by
  cases operand with
  | limit =>
    let args := appendTuple old input
    let literal : Tuple (Val model.value) [wordPort] := .cons p.limit .nil
    exact read_newest .head model args (p.row.eval model args PUnit.unit) literal
  | bank slot => exact suffix_get input old (argumentPort arity slot)
  | computed index => exact producer_read p input old fr agree index

private theorem read_column {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    {ports : List PortTy} (column : Wires (bankArgs arity) p.rowPast ports) :
    let args := appendTuple old input
    Wires.read (column.map (fun _ wire => joinedOrigin (past := []) (sigs := rowSigs p.updates)
      (tail := p.guardSigs) (keepOrigin p.test wire))) args (p.graph.header.eval model args PUnit.unit) =
      column.read args (p.row.eval model args PUnit.unit) := by
  induction column with
  | nil => rfl
  | cons wire rest ih =>
    let args := appendTuple old input
    change Tuple.cons (read model (joinedOrigin (past := []) (sigs := rowSigs p.updates)
      (tail := p.guardSigs) (keepOrigin p.test wire)) args (p.graph.header.eval model args PUnit.unit)) _ =
      Tuple.cons (read model wire args (p.row.eval model args PUnit.unit)) _
    let locals := p.row.eval model args PUnit.unit
    have head := (read_joined p.row p.test (keepOrigin p.test wire) args PUnit.unit).trans
      (read_keepOrigin p.test wire model args locals)
    exact congrArg₂ Tuple.cons head ih

/-- The two guard producers do not change any of the row's feedback operands. -/
theorem feedback_latch {arity : Nat} (p : Plan arity) (input old : WordTuple arity) :
    let args := appendTuple old input
    p.graph.latch model .backedge args (p.graph.header.eval model args PUnit.unit) = p.nextBank input old :=
  read_column p input old p.feedbackColumn

theorem native_step {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    p.graph.step model input old =
      if p.guardWord old = 0 then .inl (p.exitValue old) else .inr (p.nextBank input old) := by
  let args := appendTuple old input
  let locals := p.row.eval model args PUnit.unit
  let ready := p.guardSetup.eval model args locals
  have test : read model p.graph.predicate args (p.graph.header.eval model args PUnit.unit) =
      ⟨p.comparison.target.eval (p.guardValue old) (p.guardRhsValue old)⟩ := by
    refine (read_joined p.row p.test p.testPredicate args PUnit.unit).trans ?_
    refine (read_joined p.guardSetup (.cons p.comparison.source p.guardOperands .nil)
      (newest .head) args locals).trans ?_
    let result : Tuple (Val model.value) [(.value .predicate : PortTy)] :=
      .cons (model.run p.comparison.source (p.guardOperands.read args ready)) .nil
    refine (read_newest .head model args ready result).trans ?_
    have left := (read_keepOrigin p.guardSetup p.guardWire model args locals).trans
      (producer_read p input old fr agree p.guardIndex)
    have right : read model p.guardRhsWire args ready = p.guardRhsValue old :=
      setup_rhs_read p input old fr agree p.guardOperand
    change model.run p.comparison.source
      (.cons (read model (keepOrigin p.guardSetup p.guardWire) args ready)
        (.cons (read model p.guardRhsWire args ready) .nil)) = _
    rw [left, right]
    cases p.comparison <;> rfl
  have exit : read model p.graph.result args (p.graph.header.eval model args PUnit.unit) = p.exitValue old :=
    (read_joined p.row p.test (keepOrigin p.test p.exitWire) args PUnit.unit).trans
      ((read_keepOrigin p.test p.exitWire model args locals).trans (exit_read p input old fr agree))
  unfold Graph.step
  dsimp only
  rw [test, feedback_latch p input old, exit]
  change (if p.comparison.target.eval (p.guardValue old) (p.guardRhsValue old) then
    Sum.inr (p.nextBank input old) else Sum.inl (p.exitValue old)) = _
  unfold Plan.guardWord
  cases p.comparison.target.eval (p.guardValue old) (p.guardRhsValue old) <;> rfl

private theorem emit_append {args : List PortTy} {past sigs tail : List (List PortTy)}
    (flow : Dataflow WordOp args past sigs) (rest : Dataflow WordOp args (extend past sigs) tail) :
    emitOpsWith (fun p => .arg p.index) (appendFlow flow rest) =
      emitOpsWith (fun p => .arg p.index) flow ++ emitOpsWith (fun p => .arg p.index) rest := by
  induction flow with
  | nil => rfl
  | cons op wires next ih =>
    simp only [appendFlow, emitOpsWith, List.cons_append]
    exact congrArg (List.cons _) (ih rest)

private theorem row_length {arity : Nat} (p : Plan arity) : p.rowPast.length = p.updates.length := by
  simp [extend_rowSigs]

private theorem compare_length {arity : Nat} (p : Plan arity) : p.comparePast.length = p.compareIndex := by
  cases selected : p.guardOperand <;>
    simp [Plan.comparePast, Plan.compareIndex, selected, guardSetupSigs, extend, row_length]

private theorem setup_ops {arity producers : Nat} {past : List (List PortTy)} (limit : Word)
    (operand : GuardOperand arity producers) :
    emitOpsWith (fun p => .arg p.index) (guardSetup (past := past) limit operand) =
      (match operand with
        | .limit => [.const (.node past.length) limit]
        | .bank _ | .computed _ => []) := by
  cases operand <;> rfl

private theorem setup_length {arity : Nat} (p : Plan arity) :
    (emitOpsWith (fun p => .arg p.index) p.guardSetup).length = (guardSetupSigs p.guardOperand).length := by
  rw [Plan.guardSetup, setup_ops]
  cases p.guardOperand <;> rfl

private theorem emit_comparison {args : List PortTy} {past : List (List PortTy)}
    (cmp : Guard) (dest : Reg) (left right : Origin args past wordPort) :
    emitOpWith (fun p => .arg p.index) dest cmp.source (.cons left (.cons right .nil)) =
      .binary (.cmp cmp.target) dest (register left.address) (register right.address) := by
  cases cmp <;> cases left <;> cases right <;> rfl

private def comparisonOp {arity : Nat} (p : Plan arity) : Op Reg :=
  .binary (.cmp p.comparison.target) (.node p.compareIndex) (.node p.guardIndex.val)
    (register p.guardRhsWire.address)

private theorem emitted_ops {arity : Nat} (p : Plan arity) :
    (bankHeader p.graph).ops = emitOpsWith (fun p => .arg p.index) p.row ++
      (emitOpsWith (fun p => .arg p.index) p.guardSetup ++ [comparisonOp p]) := by
  let left := keepOrigin p.guardSetup p.guardWire
  let right := p.guardRhsWire
  have leftReg : register left.address = .node p.guardIndex.val := keep_register p.guardSetup p.guardWire
  change emitOpsWith (fun p => .arg p.index)
    (appendFlow p.row (appendFlow p.guardSetup (.cons p.comparison.source p.guardOperands .nil))) = _
  rw [emit_append p.row, emit_append p.guardSetup]
  change _ ++ (_ ++ [
    emitOpWith (fun p => .arg p.index) (.node p.comparePast.length)
      p.comparison.source (.cons left (.cons right .nil))]) = _
  rw [emit_comparison, leftReg, compare_length]
  rfl

private theorem prefix_ops_length {arity : Nat} (p : Plan arity) :
    (emitOpsWith (fun p => .arg p.index) p.row ++
      emitOpsWith (fun p => .arg p.index) p.guardSetup).length = p.compareIndex := by
  have rowSize : (emitOpsWith (fun p => .arg p.index) p.row).length = p.updates.length :=
    emit_row_length (argumentPort arity) [] p.updates
  rw [List.length_append, rowSize, setup_length]
  rfl

theorem guard_compare_operand {arity : Nat} (p : Plan arity) :
    (bankHeader p.graph).ops[p.compareIndex]? =
      some (.binary (.cmp p.comparison.target) (.node p.compareIndex) (.node p.guardIndex.val)
        (register p.guardRhsWire.address)) := by
  change _ = some (comparisonOp p)
  rw [emitted_ops, ← List.append_assoc, List.getElem?_append_right (by rw [prefix_ops_length]),
    prefix_ops_length, Nat.sub_self]
  rfl

theorem guard_compare_computed {arity : Nat} (p : Plan arity) (right : Fin p.updates.length)
    (selected : p.guardOperand = .computed right) :
    (bankHeader p.graph).ops[p.compareIndex]? =
      some (.binary (.cmp p.comparison.target) (.node p.compareIndex) (.node p.guardIndex.val) (.node right.val)) := by
  rw [guard_compare_operand]
  change some (Op.binary (.cmp p.comparison.target) (.node p.compareIndex) (.node p.guardIndex.val)
    (register (guardRhsWire p.producerWire p.guardOperand).address)) = _
  rw [selected]
  rfl

private theorem column_registers {arity : Nat} (p : Plan arity) {ports : List PortTy}
    (column : Wires (bankArgs arity) p.rowPast ports) :
    (Wires.addresses (column.map (fun _ wire => joinedOrigin (past := []) (sigs := rowSigs p.updates)
      (tail := p.guardSigs) (keepOrigin p.test wire)))).map register = column.addresses.map register := by
  induction column with
  | nil => rfl
  | cons wire rest ih =>
    change register (joinedOrigin (past := []) (sigs := rowSigs p.updates)
      (tail := p.guardSigs) (keepOrigin p.test wire)).address :: _ = register wire.address :: _
    rw [joined_register, keep_register]
    exact congrArg (List.cons _) ih

theorem feedback_registers {arity : Nat} (p : Plan arity) :
    bankIncoming p.graph .backedge = emitColumn (arity := arity) p.feedbackColumn :=
  column_registers p p.feedbackColumn

private theorem exit_register {arity : Nat} (p : Plan arity) :
    register p.graph.result.address = register p.exitWire.address :=
  (joined_register (past := []) (sigs := rowSigs p.updates) (tail := p.guardSigs)
    (keepOrigin p.test p.exitWire)).trans (keep_register p.test p.exitWire)

theorem exit_operand {arity : Nat} (p : Plan arity) :
    (bankHeader p.graph).term.args[1]? = some (2, [register p.exitWire.address]) := by
  change some (2, [register p.graph.result.address]) = _
  rw [exit_register]

private theorem guard_register {arity : Nat} (p : Plan arity) :
    register p.graph.predicate.address = .node p.compareIndex := by
  let last : Origin (bankArgs arity) (p.comparePast ++ [[.value .predicate]]) (.value .predicate) :=
    newest .head
  calc
    _ = register p.testPredicate.address :=
      joined_register (past := []) (sigs := rowSigs p.updates) (tail := p.guardSigs) p.testPredicate
    _ = register last.address :=
      joined_register (past := p.rowPast) (sigs := guardSetupSigs p.guardOperand) (tail := [[.value .predicate]]) last
    _ = .node p.comparePast.length := newest_register .head
    _ = .node p.compareIndex := congrArg Reg.node (compare_length p)

private theorem set_after_row {arity : Nat} (p : Plan arity) (fr : Frame Reg) (value : Word)
    (index : Nat) (afterRow : p.updates.length ≤ index) (wire : Origin (bankArgs arity) p.rowPast wordPort) :
    (fr.set (.node index) value).get (register wire.address) = fr.get (register wire.address) := by
  cases wire with
  | arg port => simp [Origin.address, register]
  | output i port =>
    have before : i.val < p.updates.length := by simpa only [row_length] using i.isLt
    simp [Origin.address, register, show i.val ≠ index by omega]

private theorem setup_frame_read {arity : Nat} (p : Plan arity) (fr : Frame Reg)
    (wire : Origin (bankArgs arity) p.rowPast wordPort) :
    (p.guardSetupFrame fr).get (register wire.address) = fr.get (register wire.address) := by
  cases selected : p.guardOperand with
  | limit =>
    simpa only [Plan.guardSetupFrame, selected] using
      set_after_row p fr p.limit p.updates.length (Nat.le_refl _) wire
  | bank _ | computed _ => simp [Plan.guardSetupFrame, selected]

private theorem test_frame_read {arity : Nat} (p : Plan arity) (fr : Frame Reg)
    (old : WordTuple arity) (wire : Origin (bankArgs arity) p.rowPast wordPort) :
    (p.testFrame fr old).get (register wire.address) = (p.rowFrame fr old).get (register wire.address) :=
  (set_after_row p (p.guardSetupFrame (p.rowFrame fr old)) (p.guardWord old) p.compareIndex
    (Nat.le_add_right _ _) wire).trans (setup_frame_read p (p.rowFrame fr old) wire)

private theorem branch {arity : Nat} (p : Plan arity) (entry : Block Reg) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    step (lowerBankFrom p.graph entry) ⟨⟨0, 1, (bankHeader p.graph).ops.length⟩, p.testFrame fr old, [], mem⟩ =
      .running (p.successor input old fr mem) := by
  let after := p.testFrame fr old
  let exitReg := register p.exitWire.address
  have testValue : (p.testFrame fr old).get (.node p.compareIndex) = some (p.guardWord old) := by
    simp [Plan.testFrame]
  have block : (lowerBankFrom p.graph entry).block? 0 1 = some (bankHeader p.graph) := rfl
  have term : (bankHeader p.graph).term = .cond (.node p.compareIndex)
      1 (bankIncoming p.graph .backedge) 2 [exitReg] := by
    unfold bankHeader
    rw [guard_register, exit_register]
  have fetched := Prog.fetch_term block
  simp only [step, fetched, term]
  rw [testValue]
  change transfer (lowerBankFrom p.graph entry) ⟨⟨0, 1, (bankHeader p.graph).ops.length⟩, after, [], mem⟩
    (if p.guardWord old = 0 then 2 else 1)
    (if p.guardWord old = 0 then [exitReg] else bankIncoming p.graph .backedge) = _
  by_cases halt : p.guardWord old = 0
  · rw [ite_eq_left halt, ite_eq_left halt]
    have readRow := row_word_reads p input old fr agree p.exitWire
    have value : (p.rowFrame fr old).get exitReg = some (p.exitValue old) :=
      readRow.trans (congrArg some (exit_read p input old fr agree))
    have readExit : after.get exitReg = some (p.exitValue old) :=
      (test_frame_read p fr old p.exitWire).trans value
    have target : (lowerBankFrom p.graph entry).block? 0 2 = some exitBlock := rfl
    simp [transfer, Frame.readAll, readExit, target, exitBlock, Frame.writeAll, Plan.successor, halt]
    rfl
  · rw [ite_eq_right halt, ite_eq_right halt]
    have reads : after.readAll (bankIncoming p.graph .backedge) = some (words (p.nextBank input old)) := by
      rw [feedback_registers]
      exact readColumn_eq (arity := arity) p.feedbackColumn (appendTuple old input)
        (p.row.eval model (appendTuple old input) PUnit.unit) after
        (fun wire => (test_frame_read p fr old wire).trans (row_word_reads p input old fr agree wire))
    rw [Plan.successor, ite_eq_right halt]
    exact Routing.Proofs.transfer_bank_from p.graph entry _ _ _ rfl reads

theorem testFrame_args {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    ArgsMatch (p.testFrame fr old) (appendTuple old input) := by
  intro port
  exact (test_frame_read p fr old (.arg port)).trans (row_word_reads p input old fr agree (.arg port))

private theorem counted_append {program : Prog Reg} {n k : Nat} {s middle finish : State Reg}
    (first : StepsNWithin program [] n s middle) (rest : StepsNWithin program [] k middle finish) :
    StepsNWithin program [] (n + k) s finish := by
  induction first with
  | refl => simpa only [Nat.zero_add] using rest
  | head step _ ih =>
    rw [Nat.succ_add]
    exact .head step (ih rest)

private theorem machine_rhs_read {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    (p.guardSetupFrame (p.rowFrame fr old)).get
      (register p.guardRhsWire.address) = some (p.guardRhsValue old) := by
  change (p.guardSetupFrame (p.rowFrame fr old)).get
    (register (guardRhsWire p.producerWire p.guardOperand).address) = _
  cases selected : p.guardOperand with
  | limit =>
    have reg : register (guardRhsWire p.producerWire .limit).address =
        .node p.updates.length := by
      change register (newest (past := p.rowPast) (head := [wordPort]) .head :
        Origin (bankArgs arity) _ wordPort).address = _
      rw [newest_register, row_length]
    rw [reg]
    simp [Plan.guardSetupFrame, Plan.guardRhsValue, selected, GuardOperand.eval]
  | bank slot =>
    let wire : Origin (bankArgs arity) p.rowPast wordPort :=
      .arg (suffixPort (wordPorts arity) (argumentPort arity slot))
    change (p.guardSetupFrame (p.rowFrame fr old)).get (register wire.address) = _
    exact (setup_frame_read p (p.rowFrame fr old) wire).trans
      ((row_word_reads p input old fr agree wire).trans (congrArg some
        ((suffix_get input old (argumentPort arity slot)).trans
          (by simp [Plan.guardRhsValue, selected, GuardOperand.eval]))))
  | computed index =>
    exact (setup_frame_read p (p.rowFrame fr old) (p.producerWire index)).trans
      (by simpa only [Plan.guardRhsValue, selected, GuardOperand.eval] using
        row_producer_reads p old fr index)

private theorem guard_setup_steps {arity : Nat} (p : Plan arity) (entry : Block Reg) (old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) :
    StepsNWithin (lowerBankFrom p.graph entry) [] (guardSetupSigs p.guardOperand).length
      ⟨⟨0, 1, p.updates.length⟩, p.rowFrame fr old, [], mem⟩
      ⟨⟨0, 1, p.compareIndex⟩, p.guardSetupFrame (p.rowFrame fr old), [], mem⟩ := by
  cases selected : p.guardOperand with
  | limit =>
    let pc := p.updates.length
    let row := p.rowFrame fr old
    let literal : Op Reg := .const (.node pc) p.limit
    have block : (lowerBankFrom p.graph entry).block? 0 1 = some (bankHeader p.graph) := rfl
    have setup : emitOpsWith (fun p => .arg p.index) p.guardSetup = [literal] := by
      simp only [Plan.guardSetup, setup_ops, selected, row_length, literal, pc]
    have rowSize : (emitOpsWith (fun p => .arg p.index) p.row).length = pc :=
      emit_row_length (argumentPort arity) [] p.updates
    have fetched : (bankHeader p.graph).ops[pc]? = some literal := by
      rw [emitted_ops, List.getElem?_append_right (by rw [rowSize]), rowSize, Nat.sub_self, setup]
      rfl
    have moved := Transition.op (s := (⟨⟨0, 1, pc⟩, row, [], mem⟩ : State Reg))
      (Prog.fetch_op block fetched)
      (rfl : literal.exec row mem = some (row.set (.node pc) p.limit, mem))
    have path : StepsNWithin (lowerBankFrom p.graph entry) [] 1
        ⟨⟨0, 1, pc⟩, row, [], mem⟩
        ⟨⟨0, 1, pc + 1⟩, row.set (.node pc) p.limit, [], mem⟩ :=
      .head ⟨moved.step_eq, List.nil_suffix⟩ .refl
    simpa [pc, row, Plan.compareIndex, Plan.guardSetupFrame, guardSetupSigs, selected] using path
  | bank _ | computed _ =>
    simp only [selected, guardSetupSigs, List.length_nil, Plan.compareIndex, Plan.guardSetupFrame,
      Nat.add_zero]
    exact .refl

theorem header_activation_steps_from {arity : Nat} (p : Plan arity) (entry : Block Reg) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    StepsNWithin (lowerBankFrom p.graph entry) [] p.activationSteps ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (p.successor input old fr mem) := by
  let row := p.rowFrame fr old
  let ready := p.guardSetupFrame row
  let cmp := comparisonOp p
  have block : (lowerBankFrom p.graph entry).block? 0 1 = some (bankHeader p.graph) := rfl
  have prefixPath := row_stepsN_at (argumentPort arity) (lowerBankFrom p.graph entry) (bankHeader p.graph)
    block input old mem p.updates [] [] rfl
      (emitOpsWith (fun p => .arg p.index) p.guardSetup ++ [cmp]) (emitted_ops p) fr agree
  have toRow : StepsNWithin (lowerBankFrom p.graph entry) [] p.updates.length
      ⟨⟨0, 1, 0⟩, fr, [], mem⟩ ⟨⟨0, 1, p.updates.length⟩, row, [], mem⟩ := by
    simpa only [List.length_nil, Nat.zero_add, row, Plan.rowFrame] using prefixPath
  have toCompare := counted_append toRow (guard_setup_steps p entry old fr mem)
  have length : (bankHeader p.graph).ops.length = p.compareIndex + 1 := by
    rw [emitted_ops, ← List.append_assoc, List.length_append, prefix_ops_length]
    rfl
  have leftRead : ready.get (.node p.guardIndex.val) = some (p.guardValue old) :=
    (setup_frame_read p row p.guardWire).trans (row_producer_reads p old fr p.guardIndex)
  have rightRead := machine_rhs_read p input old fr agree
  change ready.get (register p.guardRhsWire.address) = _ at rightRead
  have cmpExec : cmp.exec ready mem = some (p.testFrame fr old, mem) := by
    simp only [cmp, comparisonOp, Op.exec, leftRead, rightRead]
    rfl
  have fetchCmp : (bankHeader p.graph).ops[p.compareIndex]? = some cmp := guard_compare_operand p
  have compareStep := Transition.op (s := (⟨⟨0, 1, p.compareIndex⟩, ready, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchCmp) cmpExec
  have branchStep := branch p entry input old fr mem agree
  rw [length] at branchStep
  exact counted_append toCompare (.head ⟨compareStep.step_eq, List.nil_suffix⟩
    (.head ⟨branchStep, List.nil_suffix⟩ .refl))

theorem header_activation_steps {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    StepsNWithin (lowerBank p.graph) [] p.activationSteps ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (p.successor input old fr mem) :=
  header_activation_steps_from p (bankPreheader p.graph) input old fr mem agree

theorem header_activation {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (lowerBank p.graph) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (p.successor input old fr mem) :=
  (header_activation_steps p input old fr mem agree).toStepsWithin.toSteps

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs
