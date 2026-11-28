module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Thms
public import Silmaril.SSA.PhiView.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Proofs

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Terminator)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame Opcode packValues)
open Silmaril.Machine.RTL.SSA (Block Func Prog StepsNWithin step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg)
open Silmaril.SSA.PhiView (readArguments)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {scope : List Reg} {width tests old new : Nat} {fn : Func Reg}
variable {entrySigs sigs : List (List PortTy)}

theorem key_injective : Function.Injective (@key tests) := by
  intro a b equal
  have source := congrArg Prod.fst equal
  revert source
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
  · intro _
    rfl
  · change 0 = 3 + _ → _
    omega
  · change 3 + _ = 0 → _
    omega
  · intro same
    apply congrArg Fin.succ
    apply Fin.ext
    change 3 + i.val = 3 + j.val at same
    omega

theorem checkPacket_registers {regs : List Reg} {packet : Packet scope width}
    (checked : checkPacket scope width regs = some packet) : packet.registers = regs := by
  induction width generalizing regs with
  | zero =>
    cases regs with
    | nil => cases checked; rfl
    | cons => cases checked
  | succ width ih =>
    cases regs with
    | nil => cases checked
    | cons reg rest =>
      simp only [checkPacket] at checked
      split at checked
      · rename_i found
        cases tail : checkPacket scope width rest with
        | none => simp [tail] at checked
        | some previous =>
          simp only [tail, Option.map_some, Option.some.injEq] at checked
          subst packet
          change scope[scope.idxOf reg]'(List.idxOf_lt_length_of_mem found) :: previous.registers = _
          rw [List.getElem_idxOf, ih tail]
      · cases checked

private theorem checkPacket_exists {regs : List Reg}
    (length : regs.length = width) (defined : ∀ reg ∈ regs, reg ∈ scope) :
    (checkPacket scope width regs).isSome := by
  subst width
  induction regs with
  | nil => rfl
  | cons reg rest ih =>
    have found := defined reg (by simp)
    simp [checkPacket, found, ih (fun reg member => defined reg (by simp [member]))]

theorem readColumn_roundTrip (checked : Checked fn tests) (i : Incoming tests) :
    ∃ block, fn.block? (key i).1 = some block ∧
      block.term.args[(key i).2]? = some (1, (checked.column i).registers) := by
  have accepted : readColumn fn (key i) = some (checked.column i) :=
    (Option.some_get (checked.present i)).symm
  unfold readColumn at accepted
  cases hb : fn.block? (key i).1 with
  | none => simp [hb] at accepted
  | some block =>
    cases ha : block.term.args[(key i).2]? with
    | none => simp [hb, ha] at accepted
    | some transfer =>
      obtain ⟨label, regs⟩ := transfer
      cases label with
      | zero => simp [hb, ha] at accepted
      | succ label =>
        cases label with
        | zero =>
          simp only [hb, ha] at accepted
          exact ⟨block, rfl, by rw [checkPacket_registers accepted, ha]⟩
        | succ label => simp [hb, ha] at accepted

private theorem packet_reemit (packet : Packet scope width) :
    decodeArguments scope packet.arguments = some packet.registers := by
  induction packet with
  | nil => rfl
  | cons index tail ih =>
    change (scope[index.val]?.bind fun head =>
      (decodeArguments scope tail.arguments).map (head :: ·)) = some _
    rw [ih, List.getElem?_eq_getElem index.isLt]
    rfl

theorem reemit_roundTrip (checked : Checked fn tests) (i : Incoming tests) :
    (fn.block? (key i).1).bind (fun block => block.term.args[(key i).2]?) = checked.reemit i := by
  obtain ⟨block, fetched, transfer⟩ := readColumn_roundTrip checked i
  rw [fetched, Option.bind_some, transfer]
  change some (1, (checked.column i).registers) =
    (decodeArguments fn.allDefs (checked.column i).arguments).map (fun regs => (1, regs))
  rw [packet_reemit]
  rfl

private theorem allDefs_of_defined {label index : Nat} {reg : Reg}
    (defined : fn.Defined label index reg) : reg ∈ fn.allDefs := by
  rcases defined with ⟨blockLabel, _, _, member⟩ | ⟨block, atBlock, available⟩
  · cases lookup : fn.block? blockLabel with
    | none => simp [Func.defsOf, lookup] at member
    | some block =>
      exact List.mem_flatMap.mpr ⟨block, List.mem_of_getElem? lookup, by simpa [Func.defsOf, lookup] using member⟩
  · apply List.mem_flatMap.mpr
    refine ⟨block, List.mem_of_getElem? atBlock, ?_⟩
    rcases available with parameter | ⟨op, before, output⟩
    · exact List.mem_append_left _ parameter
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨op, List.mem_of_mem_take before, output⟩)

private theorem use_of_arg {term : Silmaril.Machine.RTL.SSA.Term Reg} {label : Nat} {regs : List Reg} {reg : Reg}
    (column : (label, regs) ∈ term.args) (operand : reg ∈ regs) : reg ∈ term.uses := by
  cases term <;> simp_all [Silmaril.Machine.RTL.SSA.Term.args, Silmaril.Machine.RTL.SSA.Term.uses]
  grind

theorem extract_of_incoming (wf : fn.WellFormed)
    (incoming : ∀ i : Incoming tests, ∃ block regs,
      fn.block? (key i).1 = some block ∧ block.term.args[(key i).2]? = some (1, regs)) :
    (extract fn tests).isSome := by
  have present (i : Incoming tests) : (readColumn fn (key i)).isSome := by
    obtain ⟨block, regs, found, args⟩ := incoming i
    have member := List.mem_of_getElem? args
    simp only [readColumn, found, args]
    exact checkPacket_exists (Silmaril.Machine.RTL.SSA.params_length_of_argsMatch wf.argsMatch found member).1
      (fun _ operand => allDefs_of_defined
        (Silmaril.Machine.RTL.SSA.defined_of_usesDominated_term wf.usesDominated found (use_of_arg member operand)))
  simp [extract, wf, present]

private theorem at_dispatch (rows : Choices new old sigs tests) (first : Nat) (slot : Fin (tests + 1)) :
    ∃ block, (rows.blocks first)[slot.val]? = some block ∧
      block.term.args[0]? = some (1, emitColumn (rows.column slot)) := by
  induction rows generalizing first with
  | last column =>
    have : slot = 0 := Fin.eq_zero _
    subst slot
    exact ⟨_, rfl, rfl⟩
  | @test n selector column tail ih =>
    refine Fin.cases ?_ (fun i => ?_) slot
    · exact ⟨_, rfl, rfl⟩
    · obtain ⟨block, found, args⟩ := ih (first + 1) i
      exact ⟨block, found, args⟩

theorem extract_family (p : Source new old entrySigs sigs tests) :
    (extract (lowerFunc p) tests).isSome := by
  apply extract_of_incoming (lowerFunc_wellFormed p)
  intro i
  refine Fin.cases ?_ (fun slot => ?_) i
  · exact ⟨_, _, rfl, rfl⟩
  · obtain ⟨block, found, args⟩ := at_dispatch p.rows 3 slot
    refine ⟨block, _, ?_, args⟩
    change ([Width.preheader p.primary, header p, exitBlock] ++ p.rows.blocks 3)[3 + slot.val]? = _
    rw [List.getElem?_append_right (by simp)]
    simpa using found

private theorem packet_latch (packet : Packet scope width) (frame : Frame Reg) {values : List Word}
    (read : frame.readAll packet.registers = some values) :
    readArguments packet.arguments (snapshot scope frame) = packValues values := by
  induction packet generalizing values with
  | nil => cases read; rfl
  | cons index tail ih =>
    obtain ⟨word, rest, hr, hrest, rfl⟩ :=
      Silmaril.Machine.RTL.SSA.readAll_cons_eq_some.mp read
    change Value.pair (snapshot scope frame index.val)
      (readArguments tail.arguments (snapshot scope frame)) = _
    rw [packValues, ih hrest]
    have h : frame.get scope[index.val] = some word := hr
    simp [snapshot, h]

theorem latch_agrees (checked : Checked fn tests) (i : Incoming tests) (frame : Frame Reg)
    (values : List Word) (read : frame.readAll (checked.column i).registers = some values) :
    Silmaril.SSA.PhiView.latch checked.view (checked.edge i) (snapshot fn.allDefs frame) =
      packValues values :=
  packet_latch _ _ read

theorem selected (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (checked : Checked (lowerFunc (mapCaptures mapping p)) tests)
    (input : WordTuple new) (carried : WordTuple old) (frame : Frame Reg) (mem : Memory)
    (matchFrame : ArgsMatch frame (appendTuple carried input))
    (slot : Fin (tests + 1)) (values : WordTuple old)
    (taken : p.step (mapping.pull input) carried = .inr (slot, values)) :
    let i := slot.succ
    ∃ ready latched,
      StepsNWithin prog [] (sigs.length + 1 + slot.val)
        ⟨⟨0, 1, 0⟩, frame, [], mem⟩ ⟨⟨0, (key i).1, 0⟩, ready, [], mem⟩ ∧
      (checked.column i).registers = emitColumn ((mapCaptures mapping p).rows.column slot) ∧
      Eval (Opcode.step (sigs := []) prog.oracle) (snapshot (lowerFunc (mapCaptures mapping p)).allDefs ready)
        (.br 1 (checked.edge i).argument) mem 1 (packValues (words values)) mem ∧
      step prog ⟨⟨0, (key i).1, 0⟩, ready, [], mem⟩ =
        .running ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      ArgsMatch latched (appendTuple values input) := by
  let i : Incoming tests := slot.succ
  have activation := checked_activation mapping p accepted input carried frame mem matchFrame
  rw [taken] at activation
  obtain ⟨ready, latched, block, path, found, args, read, transfers, matched⟩ := activation
  obtain ⟨actual, fetched, roundTrip⟩ := readColumn_roundTrip checked i
  have progEq := (lowerChecked_sound mapping p accepted).2.1
  rw [progEq] at found
  have same : actual = block := Option.some.inj (fetched.symm.trans found)
  subst actual
  have column : (checked.column i).registers = emitColumn ((mapCaptures mapping p).rows.column slot) :=
    congrArg Prod.snd (Option.some.inj (roundTrip.symm.trans args))
  refine ⟨ready, latched, path, column, ?_, transfers, matched⟩
  apply (Silmaril.SSA.PhiView.latch_eq_transfer _ checked.view (checked.edge i) _ _ _ _ _).mpr
  exact ⟨rfl, (latch_agrees checked i ready (words values) (column ▸ read)).symm, rfl⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Proofs
