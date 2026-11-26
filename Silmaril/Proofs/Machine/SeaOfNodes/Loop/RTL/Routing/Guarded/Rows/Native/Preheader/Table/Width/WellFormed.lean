module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Defs

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Proofs

open Silmaril.Machine.RTL.SSA (Block Func Op Term)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL
  (PortTy Reg WordOp emitOpsWith emitOpsWithResults emitOpWithResults registerWithResults)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.RVSDG (Origin Port Wires extend)

variable {captures bank : Nat} {ports : List PortTy} {past sigs entrySigs : List (List PortTy)}

private theorem arg_mem (base count index : Nat) :
    Reg.arg index ∈ paramRegs base count ↔ base ≤ index ∧ index < base + count := by
  simp [paramRegs, List.mem_range'_1]

theorem layout_disjoint (captures bank : Nat) :
    List.Disjoint (paramRegs 0 captures) (paramRegs captures bank) ∧
    (∀ i, resultReg captures bank i ∉ paramRegs 0 captures ++ paramRegs captures bank) ∧
    (∀ i, Reg.node i ∉ paramRegs 0 captures ++ paramRegs captures bank ∧
      ∀ j, Reg.node i ≠ resultReg captures bank j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hc hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    have := (arg_mem _ _ _).mp hc
    have := (arg_mem _ _ _).mp hb
    omega
  · intro i
    simp only [resultReg, List.mem_append, arg_mem]
    omega
  · intros
    simp [paramRegs, resultReg]

private theorem port_lt {t : PortTy} (port : Port ports t) : port.index < ports.length := by
  induction port with
  | head => simp [Port.index]
  | tail _ ih => simpa [Port.index] using Nat.succ_lt_succ ih

private theorem ports_length (n : Nat) : (wordPorts n).length = n := by
  simp

private theorem wires_length {ts : List PortTy} (wires : Wires ports past ts) :
    wires.addresses.length = ts.length := by
  induction wires with
  | nil => rfl
  | cons _ _ ih => simp [Wires.addresses, ih]

private theorem extend_length (past sigs : List (List PortTy)) :
    (extend past sigs).length = past.length + sigs.length := by
  induction sigs generalizing past with
  | nil => rfl
  | cons _ _ ih =>
    simp only [extend, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private def emit (result : Nat → Reg) (flow : Dataflow WordOp ports past sigs) : List (Op Reg) :=
  emitOpsWithResults (fun p => .arg p.index) result flow

private theorem emit_node (flow : Dataflow WordOp ports past sigs) :
    emit Reg.node flow = emitOpsWith (fun p => .arg p.index) flow := by
  induction flow with
  | nil => rfl
  | cons op wires rest ih =>
    change _ :: emit Reg.node rest = _ :: emitOpsWith _ rest
    rw [ih]
    rfl

private theorem emit_defs (result : Nat → Reg) (flow : Dataflow WordOp ports past sigs) :
    (emit result flow).map Op.defs = (List.range' past.length sigs.length).map (fun i => [result i]) := by
  induction flow with
  | nil => rfl
  | cons op wires rest ih =>
    simp only [emit, emitOpsWithResults, List.map_cons, List.length_cons, List.range'_succ]
    change _ :: (emit result rest).map Op.defs = _
    rw [ih]
    cases op <;> simp only [List.length_append, List.length_singleton] <;> rfl

private theorem emit_length (result : Nat → Reg) (flow : Dataflow WordOp ports past sigs) :
    (emit result flow).length = sigs.length := by
  simpa only [List.length_map, List.length_range'] using congrArg List.length (emit_defs result flow)

private theorem emit_flat_defs (result : Nat → Reg) (flow : Dataflow WordOp ports past sigs) :
    (emit result flow).flatMap Op.defs = (List.range' past.length sigs.length).map result := by
  rw [List.flatMap_def, emit_defs]
  induction List.range' past.length sigs.length with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private def InScope (ports : List PortTy) (result : Nat → Reg) (pc : Nat) (r : Reg) : Prop :=
  (∃ i < ports.length, r = .arg i) ∨ ∃ i < pc, r = result i

private theorem origin_inScope (result : Nat → Reg) {t : PortTy} (wire : Origin ports past t) :
    InScope ports result past.length (registerWithResults (fun p => .arg p.index) result wire) := by
  cases wire with
  | arg p => exact Or.inl ⟨p.index, port_lt p, rfl⟩
  | output i _ => exact Or.inr ⟨i, i.isLt, rfl⟩

private theorem emit_uses (result : Nat → Reg) (flow : Dataflow WordOp ports past sigs)
    {pc : Nat} {instr : Op Reg} (found : (emit result flow)[pc]? = some instr) :
    ∀ r ∈ instr.uses, InScope ports result (past.length + pc) r := by
  induction flow generalizing pc with
  | nil => simp [emit, emitOpsWithResults] at found
  | @cons past sigs ins out op operands rest ih =>
    cases pc with
    | zero =>
      change some (emitOpWithResults (fun p => .arg p.index) result
        (result past.length) op operands) = some instr at found
      cases Option.some.inj found
      intro r used
      simp only [Nat.add_zero]
      cases op with
      | const _ => cases used
      | add | sub | eq | ne | slt =>
        simp only [emitOpWithResults, Op.uses] at used
        rcases List.mem_cons.mp used with rfl | later
        · exact origin_inScope _ _
        · obtain rfl := List.mem_singleton.mp later
          exact origin_inScope _ _
    | succ j =>
      have restFound : (emit result rest)[j]? = some instr := found
      simpa only [List.length_append, List.length_singleton, Nat.add_succ, Nat.succ_add] using ih restFound

private theorem resolve_address (result : Nat → Reg) {t : PortTy} (wire : Origin ports past t) :
    registerWithResults (fun p => .arg p.index) result wire =
      (match wire.address with | .arg i => .arg i | .output i _ => result i) := by
  cases wire <;> rfl

private theorem column_scope (result : Nat → Reg) {ts : List PortTy} (wires : Wires ports past ts)
    {r : Reg} (used : r ∈ wires.addresses.map (fun a =>
      match a with | .arg i => .arg i | .output i _ => result i)) :
    InScope ports result past.length r := by
  induction wires with
  | nil => cases used
  | cons wire rest ih =>
    rcases List.mem_cons.mp used with rfl | later
    · have valid := origin_inScope result wire
      rw [resolve_address] at valid
      exact valid
    · exact ih later

private theorem local_okUse {fn : Func Reg} {block : Block Reg} {label pc : Nat} {r : Reg}
    (found : fn.block? label = some block)
    (valid : r ∈ block.params ∨ ∃ op ∈ block.ops.take pc, r ∈ op.defs) :
    fn.okUse label pc r = true := by
  rw [Func.okUse, found, Bool.or_eq_true]
  left
  rw [Bool.or_eq_true]
  rcases valid with inParams | ⟨op, inPrefix, defines⟩
  · exact Or.inl (decide_eq_true inParams)
  · exact Or.inr (List.any_eq_true.mpr ⟨op, inPrefix, decide_eq_true defines⟩)

private theorem op_before (result : Nat → Reg) (flow : Dataflow WordOp ports [] sigs)
    {pc i : Nat} (before : i < pc) (bound : pc ≤ sigs.length) :
    ∃ op ∈ (emit result flow).take pc, result i ∈ op.defs := by
  have defs : ((emit result flow).take pc).map Op.defs =
      (List.range' 0 pc).map (fun j => [result j]) := by
    rw [List.map_take, emit_defs, ← List.map_take, List.take_range'_of_length_ge bound]
    rfl
  have contains : [result i] ∈ ((emit result flow).take pc).map Op.defs := by
    rw [defs]
    exact List.mem_map.mpr ⟨i, List.mem_range'.mpr ⟨i, before, by simp⟩, rfl⟩
  obtain ⟨op, present, eq⟩ := List.mem_map.mp contains
  exact ⟨op, present, by simp [eq]⟩

variable (g : Source captures bank entrySigs sigs)

private theorem header_ops : (header g).ops = emit Reg.node g.header :=
  (emit_node g.header).symm

theorem preheader_ops_length : (preheader g).ops.length = entrySigs.length :=
  emit_length (resultReg captures bank) g.preheader

theorem header_ops_length : (header g).ops.length = sigs.length := by
  rw [header_ops, emit_length]

private theorem entry_okUse {pc : Nat} {r : Reg} (bound : pc ≤ entrySigs.length)
    (valid : InScope (wordPorts captures) (resultReg captures bank) pc r) :
    (lowerFunc g).okUse 0 pc r = true := by
  apply local_okUse (block := preheader g) rfl
  rcases valid with ⟨i, lt, rfl⟩ | ⟨i, lt, rfl⟩
  · exact Or.inl ((arg_mem _ _ _).mpr ⟨Nat.zero_le _, by simpa [ports_length] using lt⟩)
  · exact Or.inr (op_before _ g.preheader lt bound)

private theorem captured_okUse {pc i : Nat} (lt : i < captures) :
    (lowerFunc g).okUse 1 pc (.arg i) = true := by
  have dominates : (lowerFunc g).Dominates 0 1 := by
    exact Silmaril.Machine.Graph.Digraph.Dominates.entry _ _
  have member : Reg.arg i ∈ (lowerFunc g).defsOf 0 := by
    change Reg.arg i ∈ (preheader g).defs
    exact List.mem_append_left _ ((arg_mem _ _ _).mpr ⟨Nat.zero_le _, by simpa using lt⟩)
  rw [Func.okUse, Bool.or_eq_true]
  right
  apply List.any_eq_true.mpr
  exact ⟨0, List.mem_range.mpr (show 0 < 3 by decide), by simp [dominates, member]⟩

private theorem header_okUse {pc : Nat} {r : Reg} (bound : pc ≤ sigs.length)
    (valid : InScope (wordPorts captures ++ wordPorts bank) Reg.node pc r) :
    (lowerFunc g).okUse 1 pc r = true := by
  rcases valid with ⟨i, lt, rfl⟩ | ⟨i, lt, rfl⟩
  · by_cases cap : i < captures
    · exact captured_okUse g cap
    · apply local_okUse (block := header g) rfl
      exact Or.inl ((arg_mem _ _ _).mpr ⟨Nat.le_of_not_gt cap, by simpa [ports_length] using lt⟩)
  · apply local_okUse (block := header g) rfl
    rw [header_ops]
    exact Or.inr (op_before _ g.header lt bound)

private theorem usesDominated : (lowerFunc g).UsesDominated := by
  unfold Func.UsesDominated Func.usesDominated
  rw [List.all_eq_true]
  intro l within
  have bound : l < 3 := List.mem_range.mp within
  match l with
  | 0 =>
    rw [show (lowerFunc g).block? 0 = some (preheader g) from rfl]
    dsimp only
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    constructor
    · intro pc within
      split
      · rename_i op found
        rw [List.all_eq_true]
        intro r used
        apply entry_okUse g
        · have lt := List.mem_range.mp within
          change pc < (emit (resultReg captures bank) g.preheader).length at lt
          exact Nat.le_of_lt (by simpa only [emit_length] using lt)
        · simpa only [List.length_nil, Nat.zero_add] using emit_uses _ g.preheader found r used
      · rfl
    · intro r used
      change r ∈ (g.phiInputs .entry).addresses.map (entryReg captures bank) at used
      change (lowerFunc g).okUse 0 (emit _ g.preheader).length r = true
      rw [emit_length]
      apply entry_okUse g (Nat.le_refl _)
      have valid : InScope (wordPorts captures) (resultReg captures bank)
          (extend [] entrySigs).length r := column_scope (resultReg captures bank) (g.phiInputs .entry) used
      simpa only [extend_length, List.length_nil, Nat.zero_add] using valid
  | 1 =>
    rw [show (lowerFunc g).block? 1 = some (header g) from rfl]
    dsimp only
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    constructor
    · intro pc within
      split
      · rename_i op found
        rw [List.all_eq_true]
        intro r used
        rw [header_ops] at found
        apply header_okUse g
        · have lt := List.mem_range.mp within
          rw [header_ops, emit_length] at lt
          exact Nat.le_of_lt lt
        · simpa only [List.length_nil, Nat.zero_add] using emit_uses _ g.header found r used
      · rfl
    · intro r used
      rw [header_ops, emit_length]
      apply header_okUse g (Nat.le_refl _)
      change r ∈ register g.predicate.address :: (emitColumn (g.phiInputs .backedge) ++
        [register g.result.address]) at used
      have resolved {t : PortTy} (wire : Origin (wordPorts captures ++ wordPorts bank) (extend [] sigs) t) :
          InScope (wordPorts captures ++ wordPorts bank) Reg.node sigs.length (register wire.address) := by
        have valid := origin_inScope Reg.node wire
        have eq : registerWithResults (fun p => .arg p.index) Reg.node wire =
            register wire.address := resolve_address Reg.node wire
        rw [eq] at valid
        simpa only [extend_length, List.length_nil, Nat.zero_add] using valid
      rcases List.mem_cons.mp used with rfl | later
      · exact resolved g.predicate
      rcases List.mem_append.mp later with back | ret
      · have valid : InScope (wordPorts captures ++ wordPorts bank) Reg.node
            (extend [] sigs).length r := column_scope Reg.node (g.phiInputs .backedge) back
        simpa only [extend_length, List.length_nil, Nat.zero_add] using valid
      · obtain rfl := List.mem_singleton.mp ret
        exact resolved g.result
  | 2 =>
    rw [show (lowerFunc g).block? 2 = some (exitBlock) from rfl]
    dsimp only
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    constructor
    · simp [exitBlock]
    · intro r used
      exact local_okUse (block := exitBlock) rfl (Or.inl used)
  | _ + 3 => omega

private theorem assignment : (lowerFunc g).SingleAssignment := by
  simp only [Func.SingleAssignment, Func.allDefs, lowerFunc, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  have entryDefs : (preheader g).defs = paramRegs 0 captures ++ paramRegs (captures + bank) entrySigs.length := by
    change paramRegs 0 captures ++ (emit (resultReg captures bank) g.preheader).flatMap Op.defs = _
    rw [emit_flat_defs]
    congr 1
    simp [paramRegs, List.range'_eq_map_range, resultReg, Function.comp_def, Nat.add_comm]
  have headerDefs : (header g).defs = paramRegs captures bank ++ (List.range' 0 sigs.length).map Reg.node := by
    simp only [Block.defs, header_ops, emit_flat_defs]
    rfl
  rw [entryDefs, headerDefs]
  change (_ ++ (_ ++ [Reg.phi])).Nodup
  have args (base count : Nat) : (paramRegs base count).Nodup :=
    (List.nodup_range').map (fun _ _ => Reg.arg.inj)
  have nodes : ((List.range' 0 sigs.length).map Reg.node).Nodup :=
    (List.nodup_range').map (fun _ _ => Reg.node.inj)
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨args _ _, args _ _, ?_⟩
    intro r hc _ he rfl
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    have hcap := (arg_mem _ _ _).mp hc
    have hentry := (arg_mem _ _ _).mp he
    omega
  · refine List.nodup_append.mpr ⟨?_, by simp, ?_⟩
    · refine List.nodup_append.mpr ⟨args _ _, nodes, ?_⟩
      intro r hb _ hn rfl
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      simp at hn
    · intro r hh _ hphi rfl
      obtain rfl := List.mem_singleton.mp hphi
      simp [paramRegs] at hh
  · intro r he _ hh rfl
    rcases List.mem_append.mp he with hc | ht
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      have hb : Reg.arg i ∈ paramRegs captures bank := by simpa [paramRegs] using hh
      exact layout_disjoint captures bank |>.1 hc hb
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
      have hb : Reg.arg i ∈ paramRegs captures bank := by simpa [paramRegs] using hh
      have htemp := (arg_mem _ _ _).mp ht
      have hbank := (arg_mem _ _ _).mp hb
      omega

theorem lowerFunc_wellFormed : (lowerFunc g).WellFormed := by
  refine ⟨?_, assignment g, usesDominated g, ?_⟩
  · simp [Func.WellFormedSig, Func.block?, lowerFunc, preheader, header, exitBlock,
      Term.okIn, Term.successors, paramRegs]
  · have entryLength := wires_length (g.phiInputs .entry)
    have feedbackLength := wires_length (g.phiInputs .backedge)
    simp [Func.ArgsMatch, Func.argsMatch, Func.block?, lowerFunc, preheader, header, exitBlock,
      Term.args, paramRegs, emitColumn, entryLength, feedbackLength]

theorem lowerChecked_of_accepted {old new : Nat} (mapping : InputMap old new)
    {g : SourceWithEntry old entrySigs sigs} {before : Checked.Phi.Targets}
    (accepted : Table.lowerChecked g = some before) :
    lowerChecked mapping g =
      some (lowerRTL (mapCaptures mapping g), Generic.lower (mapCaptures mapping g)) := by
  simp [lowerChecked, accepted, lowerFunc_wellFormed]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Proofs
