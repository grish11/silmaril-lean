module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Column
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Frame
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.FeedbackRow
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg PortTy emitOpsWith model word)
open Silmaril.SSA.SeaOfNodes.Diamond (Val read sortValue)
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin read_keepOrigin)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)

variable {payloads : Nat}

private theorem word_arguments {args : List PortTy} {fr : Frame Reg}
    {input : Tuple (Val model.value) args}
    (h : ArgsMatch fr input) (wire : Origin args [] wordPort) :
    fr.get (register wire.address) = some (read model wire input PUnit.unit) := by
  cases wire with
  | arg p => exact h p
  | output i _ => exact i.elim0

private theorem extend_addresses {args users : List PortTy} (past : List (List PortTy))
    (wires : Wires args [] users) : (extendArguments past wires).addresses = wires.addresses := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    cases wire with
    | arg p =>
      change (.arg p.index : Silmaril.SSA.RVSDG.Address) :: (extendArguments past rest).addresses =
        .arg p.index :: Wires.addresses rest
      rw [ih]
    | output i _ => exact i.elim0

private theorem feedback_registers (r : BankRoutes payloads) :
    r.incomingRegisters .backedge = .node 1 :: emitColumn r.feedback := by
  change .node 1 :: (extendArguments _ r.feedback).addresses.map register = _
  rw [extend_addresses]
  rfl

private theorem extend_read {args users : List PortTy} {past : List (List PortTy)}
    (wires : Wires args [] users) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) :
    (extendArguments past wires).read input locals = wires.read input PUnit.unit := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    cases wire with
    | arg p =>
      change Tuple.cons (input.get p) ((extendArguments past rest).read input locals) =
        Tuple.cons (input.get p) (Wires.read rest input PUnit.unit)
      rw [ih]
    | output i _ => exact i.elim0

theorem bank_incoming_operand (r : BankRoutes payloads) (edge : Incoming) :
    ((r.lowerFunc.block? (edge.select 0 1)).bind fun block => block.term.args[0]?) =
      some (1, r.incomingRegisters edge) := by
  cases edge <;> rfl

theorem transfer_bank_from {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs) (entry : Block Reg)
    (s : State Reg) (column : List Reg) (values : WordTuple arity)
    (func : s.point.func = 0) (reads : s.frame.readAll column = some (words values)) :
    transfer (lowerBankFrom g entry) s 1 column =
      .running ⟨⟨0, 1, 0⟩, bindWords arity s.frame values, s.stack, s.mem⟩ := by
  have target : (lowerBankFrom g entry).block? 0 1 = some (bankHeader g) := rfl
  have write : s.frame.writeAll (bankHeader g).params (words values) =
      some (bindWords arity s.frame values) := bindWords_write arity s.frame values
  simp [transfer, func, reads, target, write]

theorem transfer_bank {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs)
    (s : State Reg) (column : List Reg) (values : WordTuple arity)
    (func : s.point.func = 0) (reads : s.frame.readAll column = some (words values)) :
    transfer (lowerBank g) s 1 column =
      .running ⟨⟨0, 1, 0⟩, bindWords arity s.frame values, s.stack, s.mem⟩ :=
  transfer_bank_from g (bankPreheader g) s column values func reads

theorem step_bank_entry {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs)
    (input : WordTuple arity) (fr : Frame Reg) (stk : List (Activation Reg)) (mem : Memory)
    (agree : ArgsMatch fr input) :
    step (lowerBank g) ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindWords arity fr (g.initial model input), stk, mem⟩ := by
  have reads := readColumn_eq (arity := arity) (g.phiInputs .entry) input PUnit.unit fr (word_arguments agree)
  change transfer (lowerBank g) _ 1 (bankIncoming g .entry) = _
  exact transfer_bank g _ _ _ rfl reads

private theorem step_entry_with (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step (r.lowerWithRow updates) ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr ((r.graphWithRow updates).initial model input), stk, mem⟩ :=
  step_bank_entry (r.graphWithRow updates) input fr stk mem agree

theorem bank_step_entry (r : BankRoutes payloads) (input : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step r.lower ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.graph.initial model input), stk, mem⟩ :=
  step_entry_with r [] input fr stk mem agree

private theorem counter_read (input old : WordTuple (payloads + 1)) :
    (appendTuple old input).get (counterPort payloads) = counter old :=
  suffix_get input old .head

private theorem return_read (r : BankRoutes payloads) (input old : WordTuple (payloads + 1)) :
    (appendTuple old input).get (suffixPort (wordPorts (payloads + 1)) r.resultPort) = r.returnWord old :=
  suffix_get input old r.resultPort

private theorem nextBank_eq (r : BankRoutes payloads) (input old : WordTuple (payloads + 1)) :
    r.nextBank input old =
      .cons (counter old - 1) (r.feedback.read (appendTuple old input) PUnit.unit) := by
  let joint := appendTuple old input
  change Tuple.cons (F := Val model.value) (t := wordPort)
      (BitVec.sub (joint.get (counterPort payloads)) (1 : Word))
      ((extendArguments _ r.feedback).read joint (r.graph.header.eval model joint PUnit.unit)) = _
  rw [counter_read input old, extend_read]
  rfl

private theorem test_zero (old : WordTuple (payloads + 1)) : testWord old = 0 ↔ counter old = 0 := by
  by_cases h : counter old = 0 <;> simp [testWord, ofBool, h]

private theorem header_term (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads)) :
    (r.headerWithRow updates).term =
      .cond (.node 3) 1 (r.incomingWithRow updates .backedge) 2 [register (r.graphWithRow updates).result.address] := by
  have guard := keep_row_register updates
    (.output (3 : Fin 4) .head : Origin (headerArgs payloads) headerSigs (.value .predicate))
  change Term.cond (register (keepOrigin (rowSuffix headerSigs updates)
    (.output (3 : Fin 4) .head)).address) 1 _ 2 _ = _
  rw [guard]
  rfl

private theorem feedback_from_reads (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (old nextBank : WordTuple (payloads + 1)) (fr : Frame Reg) (stk : List (Activation Reg)) (mem : Memory)
    (reads : fr.readAll (r.incomingWithRow updates .backedge) = some (words nextBank))
    (test : fr.get (.node 3) = some (testWord old)) (taken : counter old ≠ 0) :
    step (r.lowerWithRow updates) ⟨⟨0, 1, (r.headerWithRow updates).ops.length⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr nextBank, stk, mem⟩ := by
  have fetch := Prog.fetch_term (p := r.lowerWithRow updates) (f := 0) (l := 1) (b := r.headerWithRow updates) rfl
  have nonzero := mt (test_zero old).mp taken
  simp only [step, fetch, header_term, test]
  change transfer (r.lowerWithRow updates) _
    (if testWord old = 0 then 2 else 1)
    (if testWord old = 0 then [register (r.graphWithRow updates).result.address]
      else r.incomingWithRow updates .backedge) = _
  rw [ite_eq_right nonzero, ite_eq_right nonzero]
  exact transfer_bank (r.graphWithRow updates) _ _ _ rfl reads

theorem bank_step_feedback (r : BankRoutes payloads) (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (next : fr.get (.node 1) = some (counter old - 1)) (test : fr.get (.node 3) = some (testWord old))
    (taken : counter old ≠ 0) :
    step r.lower ⟨⟨0, 1, 4⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.nextBank input old), stk, mem⟩ := by
  have payload := readColumn_eq r.feedback (appendTuple old input) PUnit.unit fr (word_arguments agree)
  have reads : fr.readAll (r.incomingRegisters .backedge) = some (words (r.nextBank input old)) := by
    rw [feedback_registers, nextBank_eq]
    simp only [Frame.readAll, List.mapM_cons, next]
    unfold Frame.readAll at payload
    rw [payload]
    rfl
  exact feedback_from_reads r [] old _ fr stk mem reads test taken

private theorem row_guard (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) :
    read model (r.graphWithRow updates).predicate (appendTuple old input)
      ((r.graphWithRow updates).header.eval model (appendTuple old input) PUnit.unit) =
      ⟨!(BEq.beq (α := Word) (counter old) 0)⟩ := by
  let joint := appendTuple old input
  let locals : Locals (Val model.value) headerSigs := r.graph.header.eval model joint PUnit.unit
  let wire : Origin (headerArgs payloads) headerSigs (.value .predicate) := .output (3 : Fin 4) .head
  change read model (keepOrigin (rowSuffix headerSigs updates) wire) joint
    ((rowSuffix headerSigs updates).eval model joint locals) = _
  rw [read_keepOrigin]
  change (⟨!(BEq.beq (α := Word) (joint.get (counterPort payloads)) 0)⟩ :
    Val model.value (.value .predicate)) = _
  rw [counter_read]

theorem source_step (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) :
    (r.graphWithRow updates).step model input old =
      if counter old = 0 then .inl (r.returnWord old) else .inr (r.nextBankWithRow updates input old) := by
  unfold Graph.step
  dsimp only
  rw [row_guard r updates input old]
  change (if (!(BEq.beq (α := Word) (counter old) 0)) = true
    then Sum.inr (α := Word) (r.nextBankWithRow updates input old)
    else Sum.inl (((appendTuple old input).get (suffixPort (wordPorts (payloads + 1)) r.resultPort)) : Word)) = _
  rw [return_read]
  by_cases h : counter old = 0 <;> (simp [h]; rfl)

private theorem get_counter {fr : Frame Reg} {input old : WordTuple (payloads + 1)}
    (agree : ArgsMatch fr (appendTuple old input)) :
    fr.get (.arg (counterPort payloads).index) = some (counter old) := by
  have got := agree (counterPort payloads)
  rw [counter_read] at got
  exact got

private theorem get_return (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    {fr : Frame Reg} {input old : WordTuple (payloads + 1)} (agree : ArgsMatch fr (appendTuple old input)) :
    fr.get (register (r.graphWithRow updates).result.address) = some (r.returnWord old) := by
  change fr.get (.arg (suffixPort (wordPorts (payloads + 1)) r.resultPort).index) = _
  have got := agree (suffixPort (wordPorts (payloads + 1)) r.resultPort)
  rw [return_read r] at got
  exact got

private theorem header_matches (updates : List (FeedbackUpdate payloads))
    {fr : Frame Reg} {input old : WordTuple (payloads + 1)}
    (agree : ArgsMatch fr (appendTuple old input)) :
    ArgsMatch (headerFrameWithRow updates fr old) (appendTuple old input) := by
  intro p
  rw [headerFrameWithRow, rowFrame_get _ _ _ _ _ (by simp)]
  simpa [headerFrame] using agree p

private def atPoint (label pc : Nat) (fr : Frame Reg) (mem : Memory) : State Reg :=
  ⟨⟨0, label, pc⟩, fr, [], mem⟩

private theorem next_counter (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) :
    counter (r.nextBankWithRow updates input old) = counter old - 1 := by
  let joint := appendTuple old input
  let locals : Locals (Val model.value) headerSigs := r.graph.header.eval model joint PUnit.unit
  let wire : Origin (headerArgs payloads) headerSigs wordPort := .output (1 : Fin 4) .head
  change (read model (keepOrigin (rowSuffix headerSigs updates) wire) joint
    ((rowSuffix headerSigs updates).eval model joint locals) : Word) = _
  rw [read_keepOrigin]
  change BitVec.sub (joint.get (counterPort payloads)) (1 : Word) = _
  rw [counter_read]
  rfl

private theorem header_read_test (updates : List (FeedbackUpdate payloads))
    (fr : Frame Reg) (old : WordTuple (payloads + 1)) :
    (headerFrameWithRow updates fr old).get (.node 3) = some (testWord old) := by
  rw [headerFrameWithRow, rowFrame_get _ _ _ _ _ (by intro j ge eq; have := Reg.node.inj eq; omega)]
  rfl

private theorem countdown_word_reads (r : BankRoutes payloads)
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (agree : ArgsMatch fr (appendTuple old input))
    (wire : Origin (headerArgs payloads) headerSigs wordPort) :
    (headerFrame fr old).get (register wire.address) =
      some (read model wire (appendTuple old input)
        (r.graph.header.eval model (appendTuple old input) PUnit.unit)) := by
  cases wire with
  | arg p => exact header_matches [] agree p
  | output i p =>
    fin_cases i <;> cases p <;> try (rename_i port; exact nomatch port)
    · rfl
    · change some (counter old - 1) = some (BitVec.sub ((appendTuple old input).get (counterPort payloads)) 1)
      rw [counter_read]
      rfl
    · rfl

private theorem header_word_reads (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (agree : ArgsMatch fr (appendTuple old input))
    (wire : Origin (headerArgs payloads) (extend [] (headerRowSigs updates)) wordPort) :
    (headerFrameWithRow updates fr old).get (register wire.address) =
      some (read model wire (appendTuple old input)
        ((r.graphWithRow updates).header.eval model (appendTuple old input) PUnit.unit)) :=
  row_reads updates headerSigs input old (headerFrame fr old)
    (r.graph.header.eval model (appendTuple old input) PUnit.unit)
    (countdown_word_reads r input old fr agree) wire

private theorem header_column_reads (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    (headerFrameWithRow updates fr old).readAll (r.incomingWithRow updates .backedge) =
      some (words (r.nextBankWithRow updates input old)) :=
  readColumn_eq (arity := payloads + 1) ((r.graphWithRow updates).phiInputs .backedge)
    (appendTuple old input) ((r.graphWithRow updates).header.eval model (appendTuple old input) PUnit.unit)
    (headerFrameWithRow updates fr old) (header_word_reads r updates input old fr agree)

theorem bank_step_feedback_with (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg) (stk : List (Activation Reg)) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple old input)) (taken : counter old ≠ 0) :
    let after := headerFrameWithRow updates fr old
    step (r.lowerWithRow updates) ⟨⟨0, 1, (r.headerWithRow updates).ops.length⟩, after, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank after (r.nextBankWithRow updates input old), stk, mem⟩ :=
  feedback_from_reads r updates old _ _ stk mem (header_column_reads r updates input old fr agree)
    (header_read_test updates fr old) taken

/-- Run the countdown instructions and the emitted feedback row. -/
private theorem header_prefix (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) {finish : State Reg}
    (tail : Steps (r.lowerWithRow updates)
      (atPoint 1 (r.headerWithRow updates).ops.length (headerFrameWithRow updates fr old) mem) finish) :
    Steps (r.lowerWithRow updates) (atPoint 1 0 fr mem) finish := by
  let one := fr.set (.node 0) 1
  let decremented := one.set (.node 1) (counter old - 1)
  let withZero := decremented.set (.node 2) 0
  have readCounter : fr.get (.arg (counterPort payloads).index) = some (counter old) := get_counter agree
  have subExec : (Op.binary .sub (.node 1) (.arg (counterPort payloads).index) (.node 0)).exec one mem = some (decremented, mem) := by
    have read : one.get (.arg (counterPort payloads).index) = some (counter old) := by simpa [one] using readCounter
    have literal : one.get (.node 0) = some 1 := rfl
    simp only [Op.exec, read, literal, Option.bind_some]
    rfl
  have testExec : (Op.binary (.cmp .ne) (.node 3) (.arg (counterPort payloads).index) (.node 2)).exec withZero mem =
      some (headerFrame fr old, mem) := by
    have read : withZero.get (.arg (counterPort payloads).index) = some (counter old) := by
      simpa [withZero, decremented, one] using readCounter
    have literal : withZero.get (.node 2) = some 0 := rfl
    simp only [Op.exec, read, literal, Option.bind_some]
    rfl
  have s₀ := Transition.op (p := r.lowerWithRow updates) (s := atPoint 1 0 fr mem)
    (o := .const (.node 0) 1) rfl (rfl : _ = some (one, mem))
  have s₁ := Transition.op (p := r.lowerWithRow updates) (s := atPoint 1 1 one mem) rfl subExec
  have s₂ := Transition.op (p := r.lowerWithRow updates) (s := atPoint 1 2 decremented mem)
    (o := .const (.node 2) 0) rfl (rfl : _ = some (withZero, mem))
  have s₃ := Transition.op (p := r.lowerWithRow updates) (s := atPoint 1 3 withZero mem) rfl testExec
  have scheduled : Steps (r.lowerWithRow updates) (atPoint 1 0 fr mem) (atPoint 1 4 (headerFrame fr old) mem) :=
    .head s₀.step_eq (.head s₁.step_eq (.head s₂.step_eq (.head s₃.step_eq .refl)))
  have ops : (r.headerWithRow updates).ops = r.header.ops ++
      emitOpsWith (fun p => .arg p.index) (rowSuffix headerSigs updates) := rfl
  have extra := row_steps (r.lowerWithRow updates) (r.headerWithRow updates) rfl input old mem
    updates headerSigs r.header.ops rfl ops (headerFrame fr old) (header_matches [] agree)
  exact scheduled.trans (extra.trans tail)

private theorem exit_step (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (fr : Frame Reg) (mem : Memory) (value : Word)
    (read : fr.get (register (r.graphWithRow updates).result.address) = some value) (halt : fr.get (.node 3) = some 0) :
    step (r.lowerWithRow updates) (atPoint 1 (r.headerWithRow updates).ops.length fr mem) =
      .running (atPoint 2 0 (fr.set .phi value) mem) := by
  have fetch := Prog.fetch_term (p := r.lowerWithRow updates) (f := 0) (l := 1) (b := r.headerWithRow updates) rfl
  have target : (r.lowerWithRow updates).block? 0 2 = some exitBlock := rfl
  simp [step, fetch, header_term, halt, transfer, Frame.readAll, target, read, atPoint, exitBlock, Frame.writeAll]

theorem bank_header_agrees_with (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (r.lowerWithRow updates) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match (r.graphWithRow updates).step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrameWithRow updates fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrameWithRow updates fr old) next, [], mem⟩) := by
  rw [source_step]
  let after := headerFrameWithRow updates fr old
  have afterAgrees := header_matches updates agree
  by_cases halt : counter old = 0
  · simp only [ite_eq_left halt]
    have read : after.get (register (r.graphWithRow updates).result.address) = some (r.returnWord old) := get_return r updates afterAgrees
    have guard : after.get (.node 3) = some 0 := by
      have test : after.get (.node 3) = some (testWord old) := header_read_test updates fr old
      rw [(test_zero old).mpr halt] at test
      exact test
    exact header_prefix r updates input old fr mem agree (.head (exit_step r updates after mem _ read guard) .refl)
  · simp only [ite_eq_right halt]
    exact header_prefix r updates input old fr mem agree
      (.head (bank_step_feedback_with r updates input old fr [] mem agree halt) .refl)

private theorem header_returns (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input : WordTuple (payloads + 1)) (mem : Memory)
    {count : Nat} {old : WordTuple (payloads + 1)} {value : sortValue model.value word}
    (source : (r.graphWithRow updates).ReturnsAfter model input count old value) :
    ∀ fr : Frame Reg, ArgsMatch fr (appendTuple old input) →
      Behaves (r.lowerWithRow updates) (atPoint 1 0 fr mem) (.returned [value] mem) := by
  refine Graph.ReturnsAfter.rec (g := (r.graphWithRow updates)) (m := model) (input := input)
    (motive := fun _ old value _ => ∀ fr, ArgsMatch fr (appendTuple old input) →
      Behaves (r.lowerWithRow updates) (atPoint 1 0 fr mem) (.returned [value] mem)) ?_ ?_ source
  · intro old value taken fr agree
    have activation := bank_header_agrees_with r updates input old fr mem agree
    rw [taken] at activation
    exact ⟨atPoint 2 0 ((headerFrameWithRow updates fr old).set .phi value) mem, activation, rfl⟩
  · intro _ old next value taken _ ih fr agree
    have activation := bank_header_agrees_with r updates input old fr mem agree
    rw [taken] at activation
    have afterAgrees := header_matches updates agree
    obtain ⟨finish, suffix, observed⟩ := ih (bindBank (headerFrameWithRow updates fr old) next)
      (bank_matches (input_matches afterAgrees) next)
    exact ⟨finish, activation.trans suffix, observed⟩

private theorem source_total (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads)) (input old : WordTuple (payloads + 1)) :
    ∃ value : Word, (r.graphWithRow updates).ReturnsAfter model input (counter old).toNat old value := by
  generalize measure : (counter old).toNat = count
  induction count generalizing old with
  | zero =>
    have halt : counter old = 0 := BitVec.eq_of_toNat_eq measure
    exact ⟨r.returnWord old, .exit ((source_step r updates input old).trans (ite_eq_left halt))⟩
  | succ count ih =>
    have more : counter old ≠ 0 := by
      intro halt
      rw [halt] at measure
      cases measure
    have positive : (1 : Word) ≤ counter old := by
      rw [BitVec.le_def]
      change 1 ≤ (counter old).toNat
      omega
    have dec : (counter (r.nextBankWithRow updates input old)).toNat = count := by
      have eq := next_counter r updates input old
      rw [eq, BitVec.toNat_sub_of_le positive]
      change (counter old).toNat - 1 = count
      omega
    obtain ⟨value, rest⟩ := ih (r.nextBankWithRow updates input old) dec
    exact ⟨value, .backedge ((source_step r updates input old).trans (ite_eq_right more)) rest⟩

private theorem source_to_oracle (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input : WordTuple (payloads + 1)) (mem : Memory) (value : Word)
    (source : (r.graphWithRow updates).Returns model input value) : (r.lowerWithRow updates).oracle 0 (words input) mem [value] mem := by
  let fr := bindWords 0 Frame.empty input
  have agree : ArgsMatch fr input := by
    intro p
    simpa only [Nat.zero_add] using bindWords_get 0 Frame.empty input p
  let initial := (r.graphWithRow updates).initial model input
  obtain ⟨_, run⟩ := source
  obtain ⟨finish, suffix, observed⟩ := header_returns r updates input mem run
    (bindBank fr initial) (bank_matches agree initial)
  have start : (r.lowerWithRow updates).start 0 (words input) mem = some (atPoint 0 0 fr mem) := by
    change ((Frame.empty.writeAll (paramRegs 0 (payloads + 1)) (words input)).map
      (fun regs => (⟨⟨0, 0, 0⟩, regs⟩ : Point × Frame Reg))).map
        (fun entered => (⟨entered.1, entered.2, [], mem⟩ : State Reg)) = _
    rw [bindWords_write]
    rfl
  exact ⟨atPoint 0 0 fr mem, start, finish, .head (step_entry_with r updates _ fr [] mem agree) suffix, observed⟩

theorem bank_returns_with_iff (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))
    (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    (r.lowerWithRow updates).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, (r.graphWithRow updates).Returns model input value ∧ returned = [value] ∧ final = initial := by
  constructor
  · intro actual
    obtain ⟨value, run⟩ := source_total r updates input ((r.graphWithRow updates).initial model input)
    have source : (r.graphWithRow updates).Returns model input value := ⟨_, run⟩
    have expected := source_to_oracle r updates input initial value source
    obtain ⟨valuesEq, memEq⟩ :=
      Prog.oracle_deterministic (r.lowerWithRow updates) 0 (words input) initial _ _ _ _ actual expected
    exact ⟨value, source, valuesEq, memEq⟩
  · rintro ⟨value, source, rfl, memEq⟩
    subst final
    exact source_to_oracle r updates input initial value source

theorem bank_header_agrees (r : BankRoutes payloads) (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrame fr old) next, [], mem⟩) := by
  have follows := bank_header_agrees_with r [] input old fr mem agree
  cases result : r.graph.step model input old <;>
    (have evaluated : (r.graphWithRow []).step model input old = _ := result
     rw [evaluated] at follows
     exact follows)

theorem bank_returns_iff (r : BankRoutes payloads) (input : WordTuple (payloads + 1))
    (initial final : Memory) (returned : List Word) :
    r.lower.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, r.graph.Returns model input value ∧ returned = [value] ∧ final = initial :=
  bank_returns_with_iff r [] input initial final returned

theorem checkFeedbackRow_eq_some_iff (payloads : Nat) (specs : List FeedbackSpec)
    (updates : List (FeedbackUpdate payloads)) :
    checkFeedbackRow payloads specs = some updates ↔
      specs.mapM (fun spec => spec.check payloads) = some updates ∧
        (updates.map FeedbackUpdate.destination).Nodup := by
  cases decoded : specs.mapM (fun spec => spec.check payloads) with
  | none => simp [checkFeedbackRow, decoded]
  | some us =>
    by_cases distinct : (us.map FeedbackUpdate.destination).Nodup
    · simp [checkFeedbackRow, decoded, distinct]
      intro eq
      simpa [← eq] using distinct
    · simp [checkFeedbackRow, decoded, distinct]
      intro eq
      simpa [← eq] using distinct

theorem checkFeedbackPlan_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (specs : List FeedbackSpec) (plan : FeedbackPlan payloads) :
    checkFeedbackPlan payloads entry feedback result specs = some plan ↔
      checkFeedbackRow payloads specs = some plan.updates ∧
        checkBankRoutes payloads entry feedback result = some plan.routes ∧
        (plan.routes.lowerFuncWithRow plan.updates).WellFormed := by
  rcases plan with ⟨routes, updates⟩
  cases row : checkFeedbackRow payloads specs with
  | none => simp [checkFeedbackPlan, row]
  | some us =>
    cases checked : checkBankRoutes payloads entry feedback result with
    | none => simp [checkFeedbackPlan, row, checked]
    | some r =>
      by_cases wf : (r.lowerFuncWithRow us).WellFormed
      · simp [checkFeedbackPlan, row, checked, wf]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, wf⟩
        · rintro ⟨rfl, rfl, _⟩
          exact ⟨rfl, rfl⟩
      · simp [checkFeedbackPlan, row, checked, wf]
        rintro rfl rfl
        exact wf

theorem lowerFeedbackRowChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (specs : List FeedbackSpec) (target : Prog Reg) :
    lowerFeedbackRowChecked payloads entry feedback result specs = some target ↔
      ∃ updates, checkFeedbackRow payloads specs = some updates ∧
        ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
          (r.lowerFuncWithRow updates).WellFormed ∧ target = r.lowerWithRow updates := by
  rw [lowerFeedbackRowChecked, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨routes, updates⟩, ok, rfl⟩
    obtain ⟨row, checked, wf⟩ := (checkFeedbackPlan_eq_some_iff _ _ _ _ _ _).mp ok
    exact ⟨updates, row, routes, checked, wf, rfl⟩
  · rintro ⟨updates, row, routes, checked, wf, rfl⟩
    exact ⟨⟨routes, updates⟩, (checkFeedbackPlan_eq_some_iff _ _ _ _ _ _).mpr ⟨row, checked, wf⟩, rfl⟩

theorem lowerFeedbackRowChecked_nil (payloads : Nat) (entry feedback : List Nat) (result : Nat) :
    lowerFeedbackRowChecked payloads entry feedback result [] =
      lowerBankChecked payloads entry feedback result := by
  have empty : checkFeedbackRow payloads [] = some [] := rfl
  cases checked : checkBankRoutes payloads entry feedback result with
  | none => simp [lowerFeedbackRowChecked, checkFeedbackPlan, empty, lowerBankChecked, checked]
  | some r =>
    by_cases wf : r.lowerFunc.WellFormed
    · simp [lowerFeedbackRowChecked, checkFeedbackPlan, FeedbackPlan.rtl, empty, lowerBankChecked, checked, wf]
    · simp [lowerFeedbackRowChecked, checkFeedbackPlan, empty, lowerBankChecked, checked, wf]

theorem lowerComputedChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (spec : FeedbackSpec) (target : Prog Reg) :
    lowerComputedChecked payloads entry feedback result spec = some target ↔
      ∃ update, spec.check payloads = some update ∧
        ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
          (r.lowerFuncWith (some update)).WellFormed ∧ target = r.lowerWith (some update) := by
  cases checked : spec.check payloads with
  | none => simp [lowerComputedChecked, lowerFeedbackRowChecked, checkFeedbackPlan, checkFeedbackRow, checked]
  | some u =>
    have row : checkFeedbackRow payloads [spec] = some [u] := by
      simp [checkFeedbackRow, checked]
    simp only [lowerComputedChecked, lowerFeedbackRowChecked_eq_some_iff, row, Option.some.injEq,
      exists_eq_left']
    rfl

private theorem cast_addresses {args newArgs users : List PortTy} (same : args = newArgs)
    (wires : Wires args [] users) :
    (same ▸ wires : Wires newArgs [] users).addresses = wires.addresses := by
  cases same
  rfl

theorem checkBankRoutes_registers {entry feedback : List Nat} {result : Nat} {r : BankRoutes payloads}
    (ok : checkBankRoutes payloads entry feedback result = some r) :
    r.incomingRegisters .entry = .arg 0 :: entry.map Reg.arg ∧
      r.incomingRegisters .backedge = .node 1 :: feedback.map Reg.arg ∧ r.result.val = result := by
  unfold checkBankRoutes at ok
  split at ok
  · rename_i valid
    cases initial : checkColumn (payloads + 1) payloads entry with
    | none => rw [initial] at ok; cases ok
    | some entryColumn =>
      rw [initial] at ok
      let size := payloads + 1
      let toHeader := wordPorts_append size size
      change (checkColumn (size + size) payloads feedback).map
        (fun next => BankRoutes.mk entryColumn (toHeader ▸ next) ⟨result, valid⟩) = _ at ok
      cases next : checkColumn (size + size) payloads feedback with
      | none => rw [next] at ok; cases ok
      | some feedbackColumn =>
        rw [next] at ok
        obtain rfl := Option.some.inj ok
        refine ⟨?_, ?_, rfl⟩
        · change .arg 0 :: emitColumn entryColumn = _
          rw [checkColumn_registers initial]
        · rw [feedback_registers]
          change .node 1 :: (toHeader ▸ feedbackColumn :
            Wires (wordPorts size ++ wordPorts size) [] (wordPorts payloads)).addresses.map register = _
          rw [cast_addresses]
          exact congrArg (List.cons (.node 1)) (checkColumn_registers next)
  · cases ok

theorem lowerBankChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (target : Prog Reg) :
    lowerBankChecked payloads entry feedback result = some target ↔
      ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
        r.lowerFunc.WellFormed ∧ target = r.lower := by
  rw [lowerBankChecked, Option.bind_eq_some_iff]
  exact exists_congr (fun r => and_congr_right (fun _ => by
    by_cases wf : r.lowerFunc.WellFormed <;> simp [wf, eq_comm]))

theorem header_agrees (r : Routes) (input old : WordTuple 4) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (payloads := 3) (headerFrame fr old) next, [], mem⟩) := by
  have follows := bank_header_agrees r.toBankRoutes input old fr mem agree
  cases result : r.graph.step model input old <;>
    (have evaluated : r.toBankRoutes.graph.step model input old = _ := result
     rw [evaluated] at follows
     exact follows)

theorem checkRoutes_registers {entry feedback : List Nat} {r : Routes}
    (ok : checkRoutes entry feedback = some r) :
    r.incomingRegisters .entry = .arg 0 :: entry.map Reg.arg ∧
      r.incomingRegisters .backedge = .node 1 :: feedback.map Reg.arg := by
  unfold checkRoutes at ok
  cases initial : checkColumn 4 3 entry with
  | none => rw [initial] at ok; cases ok
  | some entryColumn =>
    rw [initial] at ok
    change (checkColumn 8 3 feedback).map (fun next => Routes.mk entryColumn next) = _ at ok
    cases next : checkColumn 8 3 feedback with
    | none => rw [next] at ok; cases ok
    | some feedbackColumn =>
      rw [next] at ok
      obtain rfl := Option.some.inj ok
      refine ⟨?_, ?_⟩
      · change .arg 0 :: emitColumn entryColumn = _
        rw [checkColumn_registers initial]
      · change (Routes.toBankRoutes ⟨entryColumn, feedbackColumn⟩).incomingRegisters .backedge = _
        rw [feedback_registers]
        change .node 1 :: emitColumn feedbackColumn = _
        rw [checkColumn_registers next]

theorem lowerChecked_eq_some_iff (entry feedback : List Nat) (target : Prog Reg) :
    lowerChecked entry feedback = some target ↔
      ∃ r, checkRoutes entry feedback = some r ∧ r.lowerFunc.WellFormed ∧ target = r.lower := by
  cases check : checkRoutes entry feedback with
  | none => simp [lowerChecked, check]
  | some route =>
    rw [lowerChecked, check]
    change (if route.lowerFunc.WellFormed then some route.lower else none) = some target ↔ _
    by_cases wf : route.lowerFunc.WellFormed <;> simp [wf, eq_comm]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs
