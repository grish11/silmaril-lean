module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Column
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.FeedbackRow
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Frame
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Fuel

/-! # Exact typed column emission and routed-loop execution -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Activation Block Label Op Prog State Steps StepsNWithin run step transfer)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp emitOpsWith model)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Val read)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)
open Silmaril.SSA.SeaOfNodes.GVN (keepOrigin)

theorem rowFrameAt_read {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (old : WordTuple arity) (updates : List (FeedbackUpdate fields)) (pc : Nat) (fr : Frame Reg)
    (index : Fin updates.length) :
    (rowFrameAt slot old pc fr updates).get (.node (pc + index.val)) =
      some (updates[index].evalAt slot old) :=
  Proofs.rowFrameAt_read slot old updates pc fr index

theorem keep_register {args : List PortTy} {past sigs : List (List PortTy)} {t : PortTy}
    (flow : Dataflow WordOp args past sigs) (wire : Origin args past t) :
    register (keepOrigin flow wire).address = register wire.address :=
  Proofs.keep_register flow wire

theorem row_reads_at {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (updates : List (FeedbackUpdate fields)) (past : List (List PortTy))
    (input old : WordTuple arity) (fr : Frame Reg) (locals : Locals (Val model.value) past)
    (agree : ∀ wire : Origin (bankArgs arity) past wordPort,
      fr.get (register wire.address) = some (read model wire (appendTuple old input) locals))
    (wire : Origin (bankArgs arity) (extend past (rowSigs updates)) wordPort) :
    (rowFrameAt slot old past.length fr updates).get (register wire.address) =
      some (read model wire (appendTuple old input) ((rowSuffixAt slot past updates).eval model
        (appendTuple old input) locals)) :=
  Proofs.row_reads_at slot updates past input old fr locals agree wire

theorem row_stepsN_at {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (p : Prog Reg) (block : Block Reg) (found : p.block? 0 1 = some block)
    (input old : WordTuple arity) (mem : Memory)
    (updates : List (FeedbackUpdate fields)) (past : List (List PortTy))
    (prefixOps : List (Op Reg)) (prefixLength : prefixOps.length = past.length)
    (tailOps : List (Op Reg))
    (ops : block.ops = prefixOps ++ (emitOpsWith (fun p => .arg p.index) (rowSuffixAt slot past updates) ++ tailOps))
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    StepsNWithin p [] updates.length ⟨⟨0, 1, past.length⟩, fr, [], mem⟩
      ⟨⟨0, 1, past.length + updates.length⟩, rowFrameAt slot old past.length fr updates, [], mem⟩ :=
  Proofs.row_stepsN_at slot p block found input old mem updates past prefixOps prefixLength tailOps ops fr agree

theorem row_steps_at {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (p : Prog Reg) (block : Block Reg) (found : p.block? 0 1 = some block)
    (input old : WordTuple arity) (mem : Memory)
    (updates : List (FeedbackUpdate fields)) (past : List (List PortTy))
    (prefixOps : List (Op Reg)) (prefixLength : prefixOps.length = past.length)
    (tailOps : List (Op Reg))
    (ops : block.ops = prefixOps ++ (emitOpsWith (fun p => .arg p.index) (rowSuffixAt slot past updates) ++ tailOps))
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps p ⟨⟨0, 1, past.length⟩, fr, [], mem⟩
      ⟨⟨0, 1, past.length + updates.length⟩, rowFrameAt slot old past.length fr updates, [], mem⟩ :=
  Proofs.row_steps_at slot p block found input old mem updates past prefixOps prefixLength tailOps ops fr agree

theorem emit_row_length {fields arity : Nat} (slot : Fin fields → Port (wordPorts arity) wordPort)
    (past : List (List PortTy)) (updates : List (FeedbackUpdate fields)) :
    (emitOpsWith (fun p => .arg p.index) (rowSuffixAt slot past updates)).length = updates.length :=
  Proofs.emit_row_length slot past updates

theorem suffix_get {pre tail : List PortTy} {t : PortTy}
    (left : Tuple (Val model.value) pre) (right : Tuple (Val model.value) tail) (p : Port tail t) :
    (appendTuple right left).get (suffixPort pre p) = right.get p :=
  Proofs.suffix_get left right p

theorem bindWords_write {arity : Nat} (base : Nat) (fr : Frame Reg) (values : WordTuple arity) :
    fr.writeAll (paramRegs base arity) (words values) = some (bindWords base fr values) :=
  Proofs.bindWords_write base fr values

theorem bindWords_args {arity : Nat} (values : WordTuple arity) :
    ArgsMatch (bindWords 0 Frame.empty values) values :=
  Proofs.bindWords_args values

theorem bank_matches_at {arity : Nat} {fr : Frame Reg} {input : WordTuple arity}
    (agree : ArgsMatch fr input) (values : WordTuple arity) :
    ArgsMatch (bindWords arity fr values) (appendTuple values input) :=
  Proofs.bank_matches_at agree values

theorem input_matches_at {arity : Nat} {fr : Frame Reg} {input old : WordTuple arity}
    (agree : ArgsMatch fr (appendTuple old input)) : ArgsMatch fr input :=
  Proofs.input_matches_at agree

theorem run_after_prefix {program : Prog Reg} {steps : Nat} {s finish : State Reg}
    (prefixPath : StepsNWithin program [] steps s finish) {fuel : Nat} {returned : List Word} {final : Memory}
    (observed : run program fuel s = .returned returned final) :
    ∃ remaining, fuel = steps + remaining ∧ run program remaining finish = .returned returned final :=
  Proofs.run_after_prefix prefixPath observed

theorem fuel_of_steps {program : Prog Reg} {s finish : State Reg}
    (path : Steps program s finish) {returned : List Word} {final : Memory}
    (observed : step program finish = .returned returned final) :
    ∃ fuel, run program fuel s = .returned returned final :=
  Proofs.fuel_of_steps path observed

theorem run_through_prefix {program : Prog Reg} {steps : Nat} {s finish : State Reg}
    (path : StepsNWithin program [] steps s finish) (remaining : Nat) :
    run program (steps + remaining) s = run program remaining finish :=
  Proofs.run_through_prefix path remaining

theorem checkColumn_registers {scope arity : Nat} {indices : List Nat}
    {wires : ArgumentColumn scope arity} (ok : checkColumn scope arity indices = some wires) :
    emitColumn wires = indices.map Reg.arg :=
  Proofs.checkColumn_registers ok

/-- Resolve every operand in the predecessor frame before binding any
destination. This law is independent of the number of word slots. -/
theorem readColumn_eq {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (wires : Wires args past (wordPorts arity)) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) (fr : Frame Reg)
    (agree : ∀ wire : Origin args past wordPort,
      fr.get (register wire.address) = some (read model wire input locals)) :
    fr.readAll (emitColumn wires) = some (words (wires.read input locals)) :=
  Proofs.readColumn_eq wires input locals fr agree

/-- Matching native reads and a target of the declared arity give the exact
machine transfer, including the old stack and the entire memory. -/
theorem transfer_column {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (wires : Wires args past (wordPorts arity)) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) (p : Prog Reg) (s : State Reg)
    (target : Label) (block : Block Reg) (found : p.block? s.point.func target = some block)
    (arityEq : block.params.length = arity)
    (agree : ∀ wire : Origin args past wordPort,
      s.frame.get (register wire.address) = some (read model wire input locals)) :
    ∃ after, s.frame.writeAll block.params (words (wires.read input locals)) = some after ∧
      transfer p s target (emitColumn wires) =
        .running ⟨⟨s.point.func, target, 0⟩, after, s.stack, s.mem⟩ :=
  Proofs.transfer_column wires input locals p s target block found arityEq agree

/-- The bank emitter reads the whole incoming column before rebinding its
header parameters. This transfer applies to any emitted word-bank graph. -/
theorem transfer_bank {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs)
    (s : State Reg) (column : List Reg) (values : WordTuple arity)
    (func : s.point.func = 0) (reads : s.frame.readAll column = some (words values)) :
    transfer (lowerBank g) s 1 column =
      .running ⟨⟨0, 1, 0⟩, bindWords arity s.frame values, s.stack, s.mem⟩ :=
  Proofs.transfer_bank g s column values func reads

theorem step_bank_entry {arity : Nat} {sigs : List (List PortTy)} (g : BankGraph arity sigs)
    (input : WordTuple arity) (fr : Frame Reg) (stk : List (Activation Reg)) (mem : Memory)
    (agree : ArgsMatch fr input) :
    step (lowerBank g) ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindWords arity fr (g.initial model input), stk, mem⟩ :=
  Proofs.step_bank_entry g input fr stk mem agree

/-- The decoded positions become exactly the emitted register operands, in
slot order, beside the fixed incoming counter operand. -/
theorem checkRoutes_registers {entry feedback : List Nat} {r : Routes}
    (ok : checkRoutes entry feedback = some r) :
    r.incomingRegisters .entry = .arg 0 :: entry.map Reg.arg ∧
      r.incomingRegisters .backedge = .node 1 :: feedback.map Reg.arg :=
  Proofs.checkRoutes_registers ok

theorem lowerChecked_eq_some_iff (entry feedback : List Nat) (target : Prog Reg) :
    lowerChecked entry feedback = some target ↔
      ∃ r, checkRoutes entry feedback = some r ∧ r.lowerFunc.WellFormed ∧ target = r.lower :=
  Proofs.lowerChecked_eq_some_iff entry feedback target

theorem checked_wellFormed {entry feedback : List Nat} {target : Prog Reg}
    (ok : lowerChecked entry feedback = some target) : target.WellFormed := by
  obtain ⟨r, _, wf, rfl⟩ := (lowerChecked_eq_some_iff entry feedback target).mp ok
  simpa [Prog.WellFormed, Routes.lower, BankRoutes.lower, BankRoutes.lowerWith, BankRoutes.lowerWithRow, lowerBank, BankRoutes.lowerFuncWithRow] using wf

/-- Checked positions are preserved in the actual operands and return port. -/
theorem checkBankRoutes_registers {payloads : Nat} {entry feedback : List Nat} {result : Nat}
    {r : BankRoutes payloads} (ok : checkBankRoutes payloads entry feedback result = some r) :
    r.incomingRegisters .entry = .arg 0 :: entry.map Reg.arg ∧
      r.incomingRegisters .backedge = .node 1 :: feedback.map Reg.arg ∧ r.result.val = result :=
  Proofs.checkBankRoutes_registers ok

theorem lowerBankChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (target : Prog Reg) :
    lowerBankChecked payloads entry feedback result = some target ↔
      ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
        r.lowerFunc.WellFormed ∧ target = r.lower :=
  Proofs.lowerBankChecked_eq_some_iff payloads entry feedback result target

theorem lowerBankChecked_zero (entry feedback : List Nat) (result : Nat) :
    lowerBankChecked 0 entry feedback result = none := by
  simp [lowerBankChecked, checkBankRoutes]

theorem bank_checked_wellFormed {payloads : Nat} {entry feedback : List Nat} {result : Nat}
    {target : Prog Reg} (ok : lowerBankChecked payloads entry feedback result = some target) :
    target.WellFormed := by
  obtain ⟨r, _, wf, rfl⟩ := (lowerBankChecked_eq_some_iff payloads entry feedback result target).mp ok
  simpa [Prog.WellFormed, BankRoutes.lower, BankRoutes.lowerWith, BankRoutes.lowerWithRow, lowerBank, BankRoutes.lowerFuncWithRow] using wf

/-- Admission recovers the checked update, copy routes, and the machine's
SSA well-formedness proof. -/
theorem lowerComputedChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (spec : FeedbackSpec) (target : Prog Reg) :
    lowerComputedChecked payloads entry feedback result spec = some target ↔
      ∃ update, spec.check payloads = some update ∧
        ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
          (r.lowerFuncWith (some update)).WellFormed ∧ target = r.lowerWith (some update) :=
  Proofs.lowerComputedChecked_eq_some_iff payloads entry feedback result spec target

theorem computed_checked_wellFormed {payloads : Nat} {entry feedback : List Nat} {result : Nat}
    {spec : FeedbackSpec} {target : Prog Reg}
    (ok : lowerComputedChecked payloads entry feedback result spec = some target) :
    target.WellFormed := by
  obtain ⟨u, _, r, _, wf, rfl⟩ :=
    (lowerComputedChecked_eq_some_iff payloads entry feedback result spec target).mp ok
  change (r.lowerFuncWithRow [u]).WellFormed at wf
  simpa [Prog.WellFormed, BankRoutes.lowerWith, BankRoutes.lowerWithRow, lowerBank, BankRoutes.lowerFuncWithRow] using wf

section ComputedFeedback

variable {payloads : Nat} (r : BankRoutes payloads) (u : FeedbackUpdate payloads)

/-- The actual taken branch reads both the computed result and all copies
from the same producer frame before writing any payload register. -/
theorem computed_step_feedback (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (taken : counter old ≠ 0) :
    let after := headerFrameWith (some u) fr old
    step (r.lowerWith (some u)) ⟨⟨0, 1, (r.headerWith (some u)).ops.length⟩, after, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank after (r.nextBankWith (some u) input old), stk, mem⟩ :=
  Proofs.bank_step_feedback_with r [u] input old fr stk mem agree taken

/-- An actual machine header activation computes the word from the old
bank, then takes the branch selected by the independent native step. -/
theorem computed_header_agrees (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (r.lowerWith (some u)) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match (r.graphWith (some u)).step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrameWith (some u) fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrameWith (some u) fr old) next, [], mem⟩) :=
  Proofs.bank_header_agrees_with r [u] input old fr mem agree

theorem computed_returns_iff (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    (r.lowerWith (some u)).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, (r.graphWith (some u)).Returns model input value ∧
        returned = [value] ∧ final = initial :=
  Proofs.bank_returns_with_iff r [u] input initial final returned

end ComputedFeedback

theorem checkFeedbackRow_eq_some_iff (payloads : Nat) (specs : List FeedbackSpec)
    (updates : List (FeedbackUpdate payloads)) :
    checkFeedbackRow payloads specs = some updates ↔
      specs.mapM (fun spec => spec.check payloads) = some updates ∧
        (updates.map FeedbackUpdate.destination).Nodup :=
  Proofs.checkFeedbackRow_eq_some_iff payloads specs updates

theorem checkFeedbackPlan_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (specs : List FeedbackSpec) (plan : FeedbackPlan payloads) :
    checkFeedbackPlan payloads entry feedback result specs = some plan ↔
      checkFeedbackRow payloads specs = some plan.updates ∧
        checkBankRoutes payloads entry feedback result = some plan.routes ∧
        (plan.routes.lowerFuncWithRow plan.updates).WellFormed :=
  Proofs.checkFeedbackPlan_eq_some_iff payloads entry feedback result specs plan

theorem lowerFeedbackRowChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (specs : List FeedbackSpec) (target : Prog Reg) :
    lowerFeedbackRowChecked payloads entry feedback result specs = some target ↔
      ∃ updates, checkFeedbackRow payloads specs = some updates ∧
        ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
          (r.lowerFuncWithRow updates).WellFormed ∧ target = r.lowerWithRow updates :=
  Proofs.lowerFeedbackRowChecked_eq_some_iff payloads entry feedback result specs target

theorem row_checked_wellFormed {payloads : Nat} {entry feedback : List Nat} {result : Nat}
    {specs : List FeedbackSpec} {target : Prog Reg}
    (ok : lowerFeedbackRowChecked payloads entry feedback result specs = some target) :
    target.WellFormed := by
  obtain ⟨_, _, _, _, wf, rfl⟩ :=
    (lowerFeedbackRowChecked_eq_some_iff payloads entry feedback result specs target).mp ok
  simpa [Prog.WellFormed, BankRoutes.lowerWithRow, lowerBank, BankRoutes.lowerFuncWithRow] using wf

theorem lowerFeedbackRowChecked_nil (payloads : Nat) (entry feedback : List Nat) (result : Nat) :
    lowerFeedbackRowChecked payloads entry feedback result [] =
      lowerBankChecked payloads entry feedback result :=
  Proofs.lowerFeedbackRowChecked_nil payloads entry feedback result

theorem lowerFeedbackRowChecked_singleton (payloads : Nat) (entry feedback : List Nat) (result : Nat)
    (spec : FeedbackSpec) :
    lowerFeedbackRowChecked payloads entry feedback result [spec] =
      lowerComputedChecked payloads entry feedback result spec := rfl

section FeedbackRows

variable {payloads : Nat} (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))

/-- The independent native countdown step either returns the selected old
payload or latches the whole typed feedback column. -/
theorem row_native_step (input old : WordTuple (payloads + 1)) :
    (r.graphWithRow updates).step model input old =
      if counter old = 0 then .inl (r.returnWord old) else .inr (r.nextBankWithRow updates input old) :=
  Proofs.source_step r updates input old

/-- The actual taken branch reads the computed results and all copies
from the same producer frame before writing any payload register. -/
theorem row_step_feedback (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (taken : counter old ≠ 0) :
    let after := headerFrameWithRow updates fr old
    step (r.lowerWithRow updates) ⟨⟨0, 1, (r.headerWithRow updates).ops.length⟩, after, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank after (r.nextBankWithRow updates input old), stk, mem⟩ :=
  Proofs.bank_step_feedback_with r updates input old fr stk mem agree taken

/-- An actual machine header activation computes the row from the old
bank, then takes the branch selected by the independent native step. -/
theorem row_header_agrees (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (r.lowerWithRow updates) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match (r.graphWithRow updates).step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrameWithRow updates fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrameWithRow updates fr old) next, [], mem⟩) :=
  Proofs.bank_header_agrees_with r updates input old fr mem agree

theorem row_returns_iff (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    (r.lowerWithRow updates).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, (r.graphWithRow updates).Returns model input value ∧
        returned = [value] ∧ final = initial :=
  Proofs.bank_returns_with_iff r updates input initial final returned

end FeedbackRows

section ArbitraryArity

variable {payloads : Nat} (r : BankRoutes payloads)

theorem bank_incoming_operand (edge : Incoming) :
    ((r.lowerFunc.block? (edge.select 0 1)).bind fun block => block.term.args[0]?) =
      some (1, r.incomingRegisters edge) :=
  Proofs.bank_incoming_operand r edge

theorem bank_step_entry (input : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step r.lower ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.graph.initial model input), stk, mem⟩ :=
  Proofs.bank_step_entry r input fr stk mem agree

theorem bank_step_feedback (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (next : fr.get (.node 1) = some (counter old - 1)) (test : fr.get (.node 3) = some (testWord old))
    (taken : counter old ≠ 0) :
    step r.lower ⟨⟨0, 1, 4⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.nextBank input old), stk, mem⟩ :=
  Proofs.bank_step_feedback r input old fr stk mem agree next test taken

/-- One native activation determines the exact successor of the emitted RTL
header, with the selected return or the simultaneous feedback bank. -/
theorem bank_header_agrees (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrame fr old) next, [], mem⟩) :=
  Proofs.bank_header_agrees r input old fr mem agree

/-- Finite return preserves and reflects the selected word and whole memory. -/
theorem bank_returns_iff (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    r.lower.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, r.graph.Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.bank_returns_iff r input initial final returned

end ArbitraryArity

variable (r : Routes)

theorem incoming_operand (edge : Incoming) :
    ((r.lowerFunc.block? (edge.select 0 1)).bind fun block => block.term.args[0]?) =
      some (1, r.incomingRegisters edge) :=
  Proofs.bank_incoming_operand r.toBankRoutes edge

theorem step_entry (input : WordTuple 4) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step r.lower ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.graph.initial model input), stk, mem⟩ :=
  Proofs.bank_step_entry r.toBankRoutes input fr stk mem agree

theorem step_feedback (input old : WordTuple 4) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (next : fr.get (.node 1) = some (counter old - 1)) (test : fr.get (.node 3) = some (testWord old))
    (taken : counter old ≠ 0) :
    step r.lower ⟨⟨0, 1, 4⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.nextBank input old), stk, mem⟩ :=
  Proofs.bank_step_feedback r.toBankRoutes input old fr stk mem agree next test taken

/-- One independent native activation determines the exact RTL successor
state after the header's producer instructions and selected transfer. -/
theorem header_agrees (input old : WordTuple 4) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (payloads := 3) (headerFrame fr old) next, [], mem⟩) :=
  Proofs.header_agrees r input old fr mem agree

theorem lower_returns_iff (input : WordTuple 4) (initial final : Memory) (returned : List Word) :
    r.lower.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, r.graph.Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.bank_returns_iff r.toBankRoutes input initial final returned

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
