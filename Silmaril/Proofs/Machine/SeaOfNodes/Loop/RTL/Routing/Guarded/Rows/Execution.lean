module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWith emitOpWith model)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val read)
open Silmaril.SSA.SeaOfNodes.GVN
  (keepOrigin newest newestIndex weaken read_keepOrigin read_newest read_weaken)
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

private theorem guard_read {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    read model p.guardWire (appendTuple old input)
      (p.row.eval model (appendTuple old input) PUnit.unit) = p.guardValue old := by
  have observed := row_word_reads p input old fr agree p.guardWire
  change (p.rowFrame fr old).get (.node p.guardIndex.val) = _ at observed
  have computed : (p.rowFrame fr old).get (.node p.guardIndex.val) = some (p.guardValue old) := by
    simpa only [Nat.zero_add, Plan.rowFrame, Plan.guardValue] using rowFrameAt_read (argumentPort arity) old p.updates 0 fr p.guardIndex
  exact Option.some.inj (observed.symm.trans computed)

private theorem read_column {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    {ports : List PortTy} (column : Wires (bankArgs arity) p.rowPast ports) :
    let args := appendTuple old input
    Wires.read (column.map (fun _ wire => joinedOrigin (past := []) (sigs := rowSigs p.updates)
      (tail := guardSigs) (keepOrigin p.test wire))) args (p.graph.header.eval model args PUnit.unit) =
      column.read args (p.row.eval model args PUnit.unit) := by
  induction column with
  | nil => rfl
  | cons wire rest ih =>
    let args := appendTuple old input
    change Tuple.cons (read model (joinedOrigin (past := []) (sigs := rowSigs p.updates)
      (tail := guardSigs) (keepOrigin p.test wire)) args (p.graph.header.eval model args PUnit.unit)) _ =
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
  let constant : Tuple (Val model.value) [wordPort] := .cons p.limit .nil
  let limited := locals.snoc constant
  have test : read model p.graph.predicate args (p.graph.header.eval model args PUnit.unit) =
      ⟨p.comparison.target.eval (p.guardValue old) p.limit⟩ := by
    let predicate : Origin (bankArgs arity) (extend p.rowPast guardSigs) (.value .predicate) :=
      newest (past := p.rowPast ++ [[wordPort]]) .head
    refine (read_joined p.row p.test predicate args PUnit.unit).trans ?_
    let operands : Tuple (Val model.value) [wordPort, wordPort] :=
      .cons (read model (weaken [wordPort] p.guardWire) args limited)
        (.cons (read model (newest .head) args limited) .nil)
    let result : Tuple (Val model.value) [(.value .predicate : PortTy)] :=
      .cons (model.run p.comparison.source operands) .nil
    refine (read_newest .head model args limited result).trans ?_
    have left := (read_weaken p.guardWire model args locals constant).trans (guard_read p input old fr agree)
    have right := read_newest .head model args locals constant
    change model.run p.comparison.source
      (.cons (read model (weaken [wordPort] p.guardWire) args (locals.snoc constant))
        (.cons (read model (newest .head) args (locals.snoc constant)) .nil)) = _
    rw [left, right]
    cases p.comparison <;> rfl
  have exit : read model p.graph.result args (p.graph.header.eval model args PUnit.unit) = p.exitValue old :=
    suffix_get input old (argumentPort arity p.exitSlot)
  unfold Graph.step
  dsimp only
  rw [test, feedback_latch p input old, exit]
  change (if p.comparison.target.eval (p.guardValue old) p.limit then
    Sum.inr (p.nextBank input old) else Sum.inl (p.exitValue old)) = _
  unfold Plan.guardWord
  cases p.comparison.target.eval (p.guardValue old) p.limit <;> rfl

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

private theorem emit_comparison {args : List PortTy} {past : List (List PortTy)}
    (cmp : Guard) (dest : Reg) (left right : Origin args past wordPort) :
    emitOpWith (fun p => .arg p.index) dest cmp.source (.cons left (.cons right .nil)) =
      .binary (.cmp cmp.target) dest (register left.address) (register right.address) := by
  cases cmp <;> cases left <;> cases right <;> rfl

private theorem emitted_ops {arity : Nat} (p : Plan arity) :
    (bankHeader p.graph).ops = emitOpsWith (fun p => .arg p.index) p.row ++
      [.const (.node p.updates.length) p.limit,
       .binary (.cmp p.comparison.target) (.node (p.updates.length + 1))
         (.node p.guardIndex.val) (.node p.updates.length)] := by
  let left := weaken [wordPort] p.guardWire
  let right : Origin (bankArgs arity) (p.rowPast ++ [[wordPort]]) wordPort := newest .head
  let constant : Dataflow WordOp (bankArgs arity) p.rowPast [[wordPort]] := .cons (.const p.limit) .nil .nil
  have leftReg : register left.address = .node p.guardIndex.val := keep_register constant p.guardWire
  have rightReg : register right.address = .node p.rowPast.length := newest_register .head
  change emitOpsWith (fun p => .arg p.index) (appendFlow p.row p.test) = _
  rw [emit_append]
  change _ ++ [.const (.node p.rowPast.length) p.limit,
    emitOpWith (fun p => .arg p.index) (.node ((p.rowPast ++ [[wordPort]]).length))
      p.comparison.source (.cons left (.cons right .nil))] = _
  rw [emit_comparison, leftReg, rightReg, List.length_append, List.length_singleton, row_length]

private theorem column_registers {arity : Nat} (p : Plan arity) {ports : List PortTy}
    (column : Wires (bankArgs arity) p.rowPast ports) :
    (Wires.addresses (column.map (fun _ wire => joinedOrigin (past := []) (sigs := rowSigs p.updates)
      (tail := guardSigs) (keepOrigin p.test wire)))).map register = column.addresses.map register := by
  induction column with
  | nil => rfl
  | cons wire rest ih =>
    change register (joinedOrigin (past := []) (sigs := rowSigs p.updates)
      (tail := guardSigs) (keepOrigin p.test wire)).address :: _ = register wire.address :: _
    rw [joined_register, keep_register]
    exact congrArg (List.cons _) ih

theorem feedback_registers {arity : Nat} (p : Plan arity) :
    bankIncoming p.graph .backedge = emitColumn (arity := arity) p.feedbackColumn :=
  column_registers p p.feedbackColumn

private theorem guard_register {arity : Nat} (p : Plan arity) :
    register p.graph.predicate.address = .node (p.updates.length + 1) := by
  let last : Origin (bankArgs arity) (extend p.rowPast guardSigs) (.value .predicate) :=
    newest (past := p.rowPast ++ [[wordPort]]) .head
  have kept : register p.graph.predicate.address = register last.address :=
    joined_register (past := []) (sigs := rowSigs p.updates) (tail := guardSigs) last
  rw [kept, show register last.address = .node (p.rowPast ++ [[wordPort]]).length from newest_register .head,
    List.length_append, List.length_singleton, row_length]

private theorem test_frame_read {arity : Nat} (p : Plan arity) (fr : Frame Reg)
    (old : WordTuple arity) (wire : Origin (bankArgs arity) p.rowPast wordPort) :
    (p.testFrame fr old).get (register wire.address) = (p.rowFrame fr old).get (register wire.address) := by
  cases wire with
  | arg port => simp [Plan.testFrame, Origin.address, register]
  | output i port =>
    have before : i.val < p.updates.length := by simpa only [row_length] using i.isLt
    simp [Plan.testFrame, Origin.address, register, show i.val ≠ p.updates.length by omega,
      show i.val ≠ p.updates.length + 1 by omega]

private theorem branch {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    step (lowerBank p.graph) ⟨⟨0, 1, (bankHeader p.graph).ops.length⟩, p.testFrame fr old, [], mem⟩ =
      .running (p.successor input old fr mem) := by
  let after := p.testFrame fr old
  let exitPort := suffixPort (wordPorts arity) (argumentPort arity p.exitSlot)
  have exitRegister : register p.graph.result.address = .arg exitPort.index := rfl
  have testValue : (p.testFrame fr old).get (.node (p.updates.length + 1)) = some (p.guardWord old) := by
    simp [Plan.testFrame]
  have block : (lowerBank p.graph).block? 0 1 = some (bankHeader p.graph) := rfl
  have term : (bankHeader p.graph).term = .cond (.node (p.updates.length + 1))
      1 (bankIncoming p.graph .backedge) 2 [.arg exitPort.index] := by
    unfold bankHeader
    rw [guard_register, exitRegister]
  have fetched := Prog.fetch_term block
  simp only [step, fetched, term]
  rw [testValue]
  change transfer (lowerBank p.graph) ⟨⟨0, 1, (bankHeader p.graph).ops.length⟩, after, [], mem⟩
    (if p.guardWord old = 0 then 2 else 1)
    (if p.guardWord old = 0 then [.arg exitPort.index] else bankIncoming p.graph .backedge) = _
  by_cases halt : p.guardWord old = 0
  · rw [ite_eq_left halt, ite_eq_left halt]
    have readRow := row_word_reads p input old fr agree (.arg exitPort)
    have value : (p.rowFrame fr old).get (.arg exitPort.index) = some (p.exitValue old) :=
      readRow.trans (congrArg some (suffix_get input old (argumentPort arity p.exitSlot)))
    have readExit : after.get (.arg exitPort.index) = some (p.exitValue old) :=
      (test_frame_read p fr old (.arg exitPort)).trans value
    have target : (lowerBank p.graph).block? 0 2 = some exitBlock := rfl
    simp [transfer, Frame.readAll, readExit, target, exitBlock, Frame.writeAll, Plan.successor, halt]
    rfl
  · rw [ite_eq_right halt, ite_eq_right halt]
    have reads : after.readAll (bankIncoming p.graph .backedge) = some (words (p.nextBank input old)) := by
      rw [feedback_registers]
      exact readColumn_eq (arity := arity) p.feedbackColumn (appendTuple old input)
        (p.row.eval model (appendTuple old input) PUnit.unit) after
        (fun wire => (test_frame_read p fr old wire).trans (row_word_reads p input old fr agree wire))
    rw [Plan.successor, ite_eq_right halt]
    exact transfer_bank p.graph _ _ _ rfl reads

theorem header_activation {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (lowerBank p.graph) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (p.successor input old fr mem) := by
  let pc := p.updates.length
  let row := p.rowFrame fr old
  let limited := row.set (.node pc) p.limit
  let lit : Op Reg := .const (.node pc) p.limit
  let cmp : Op Reg := .binary (.cmp p.comparison.target) (.node (pc + 1)) (.node p.guardIndex.val) (.node pc)
  have block : (lowerBank p.graph).block? 0 1 = some (bankHeader p.graph) := rfl
  have prefixPath := row_steps_at (argumentPort arity) (lowerBank p.graph) (bankHeader p.graph)
    block input old mem p.updates [] [] rfl [lit, cmp] (emitted_ops p) fr agree
  have prefixLength : (emitOpsWith (fun p => .arg p.index) p.row).length = pc :=
    emit_row_length (argumentPort arity) [] p.updates
  have fetchLit : (bankHeader p.graph).ops[pc]? = some lit := by
    rw [emitted_ops, List.getElem?_append_right (by omega), prefixLength]
    simp [lit, pc]
  have fetchCmp : (bankHeader p.graph).ops[pc + 1]? = some cmp := by
    rw [emitted_ops, List.getElem?_append_right (by omega), prefixLength]
    simp [cmp, pc]
  have length : (bankHeader p.graph).ops.length = pc + 2 := by
    rw [emitted_ops, List.length_append, prefixLength]
    rfl
  have selected : row.get (.node p.guardIndex.val) = some (p.guardValue old) := by
    simpa only [Nat.zero_add, row, Plan.rowFrame, Plan.guardValue] using rowFrameAt_read (argumentPort arity) old p.updates 0 fr p.guardIndex
  have below : p.guardIndex.val ≠ pc := Nat.ne_of_lt p.guardIndex.isLt
  have leftRead : limited.get (.node p.guardIndex.val) = some (p.guardValue old) := by
    simpa [limited, below] using selected
  have rightRead : limited.get (.node pc) = some p.limit := by simp [limited]
  have cmpExec : cmp.exec limited mem = some (p.testFrame fr old, mem) := by
    simp only [cmp, Op.exec, leftRead, rightRead]
    rfl
  have constStep := Transition.op (s := (⟨⟨0, 1, pc⟩, row, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchLit) (rfl : lit.exec row mem = some (limited, mem))
  have compareStep := Transition.op (s := (⟨⟨0, 1, pc + 1⟩, limited, [], mem⟩ : State Reg))
    (Prog.fetch_op block fetchCmp) cmpExec
  have branchStep := branch p input old fr mem agree
  rw [length] at branchStep
  have toTest : Steps (lowerBank p.graph) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ ⟨⟨0, 1, pc⟩, row, [], mem⟩ := by
    simpa only [List.length_nil, Nat.zero_add, pc, row, Plan.rowFrame] using prefixPath
  exact toTest.trans (.head constStep.step_eq (.head compareStep.step_eq (.head branchStep .refl)))

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs
