module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Recognition

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs

open Silmaril.Machine.RTL.SSA (Func Op Term Block)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL
  (PortTy Reg WordOp emitOpWithResults emitOpsWithResults registerWithResults)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.RVSDG (Origin Wires extend)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

variable {arity : Nat} {past sigs : List (List PortTy)}

private theorem emit_defs (flow : Dataflow WordOp (wordPorts arity) past sigs) :
    (emit flow).map Op.defs = (List.range' past.length sigs.length).map (fun i => [resultReg arity i]) := by
  induction flow with
  | nil => rfl
  | cons op _ rest ih =>
    simp only [emit, emitOpsWithResults, List.map_cons, List.length_cons, List.range'_succ]
    change _ :: (emit rest).map Op.defs = _
    rw [ih]
    cases op <;> simp only [List.length_append, List.length_singleton] <;> rfl

private theorem emit_length (flow : Dataflow WordOp (wordPorts arity) past sigs) :
    (emit flow).length = sigs.length := by
  simpa only [List.length_map, List.length_range'] using congrArg List.length (emit_defs flow)

private def inPrefix (arity pc : Nat) (r : Reg) : Prop :=
  r ∈ paramRegs 0 arity ∨ ∃ i < pc, r = resultReg arity i

private theorem prefix_mono {pc pc' : Nat} {r : Reg} (h : inPrefix arity pc r) (le : pc ≤ pc') :
    inPrefix arity pc' r := h.imp_right (fun ⟨i, before, eq⟩ => ⟨i, Nat.lt_of_lt_of_le before le, eq⟩)

private theorem origin_inPrefix {t : PortTy} (wire : Origin (wordPorts arity) past t) :
    inPrefix arity past.length (entryReg arity wire.address) := by
  cases wire with
  | arg p =>
    exact Or.inl (List.mem_map.mpr ⟨p.index, by simpa using port_index_lt p, rfl⟩)
  | output i _ => exact Or.inr ⟨i, i.isLt, rfl⟩

private theorem resolve_eq {t : PortTy} (wire : Origin (wordPorts arity) past t) :
    registerWithResults (fun p => .arg p.index) (resultReg arity) wire =
      entryReg arity wire.address := by cases wire <;> rfl

private theorem emit_at_uses (flow : Dataflow WordOp (wordPorts arity) past sigs)
    {pc : Nat} {instr : Op Reg} (found : (emit flow)[pc]? = some instr) :
    ∀ r ∈ instr.uses, inPrefix arity (past.length + pc) r := by
  induction flow generalizing pc with
  | nil => simp [emit, emitOpsWithResults] at found
  | @cons past sigs ins out op operands rest ih =>
    cases pc with
    | zero =>
      change some (emitOpWithResults (fun p => .arg p.index) (resultReg arity)
        (resultReg arity past.length) op operands) = some instr at found
      cases Option.some.inj found
      intro r used
      cases op with
      | const _ => cases used
      | add | sub | eq | ne | slt =>
        simp only [emitOpWithResults, Op.uses, resolve_eq] at used
        rcases List.mem_cons.mp used with rfl | later
        · exact origin_inPrefix _
        · obtain rfl := List.mem_singleton.mp later
          exact origin_inPrefix _
    | succ j =>
      have restFound : (emit rest)[j]? = some instr := found
      simpa only [List.length_append, List.length_singleton, Nat.add_succ, Nat.add_zero,
        Nat.succ_add] using ih restFound

private theorem bundle_uses {pc : Nat} {ports : List PortTy} (wires : Wires (wordPorts arity) past ports)
    (enough : past.length ≤ pc) (r : Reg) (used : r ∈ wires.addresses.map (entryReg arity)) :
    inPrefix arity pc r := by
  induction wires with
  | nil => cases used
  | cons wire _ ih =>
    rcases List.mem_cons.mp used with rfl | later
    · exact prefix_mono (origin_inPrefix wire) enough
    · exact ih later

private theorem extend_length (past sigs : List (List PortTy)) :
    (extend past sigs).length = past.length + sigs.length := by
  induction sigs generalizing past with
  | nil => rfl
  | cons _ _ ih =>
    simp only [extend, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem entry_arity {past : List (List PortTy)} {width : Nat}
    (entry : Wires (wordPorts arity) past (wordPorts width)) :
    entry.addresses.length = width := by
  induction width with
  | zero => cases entry; rfl
  | succ width ih =>
    cases entry with
    | cons _ rest => exact congrArg Nat.succ (ih rest)

variable {entrySigs : List (List PortTy)}

private theorem entry_okUse (p : Plan arity entrySigs) {pc : Nat} {r : Reg}
    (bound : pc ≤ entrySigs.length) (valid : inPrefix arity pc r) :
    p.lowerFunc.okUse 0 pc r = true := by
  have found : p.lowerFunc.block? 0 = some p.preheader := rfl
  unfold Func.okUse
  rw [found, Bool.or_eq_true]
  left
  rw [Bool.or_eq_true]
  rcases valid with param | ⟨i, before, rfl⟩
  · exact Or.inl (decide_eq_true param)
  · right
    have prefDefs : ((emit p.flow).take pc).map Op.defs =
        (List.range' 0 pc).map (fun j => [resultReg arity j]) := by
      rw [List.map_take, emit_defs, ← List.map_take, List.take_range'_of_length_ge bound]
      rfl
    change ((emit p.flow).take pc).any (fun op => decide (resultReg arity i ∈ op.defs)) = true
    have listed : [resultReg arity i] ∈ ((emit p.flow).take pc).map Op.defs := by
      rw [prefDefs]
      exact List.mem_map.mpr ⟨i, List.mem_range'.mpr ⟨i, before, by simp⟩, rfl⟩
    obtain ⟨op, present, defines⟩ := List.mem_map.mp listed
    exact List.any_eq_true.mpr ⟨op, present, by simp [defines]⟩

-- A new typed preheader with the same producer signature has the same
-- definitions. Only its entry uses need to be certified again.
theorem wellFormed_reentry (p q : Plan arity entrySigs)
    (header : bankHeader p.row.graph = bankHeader q.row.graph) (wf : p.lowerFunc.WellFormed) :
    q.lowerFunc.WellFormed := by
  let before := p.lowerFunc
  let after := q.lowerFunc
  have beforeBlocks : before.blocks = [p.preheader, bankHeader p.row.graph, exitBlock] := rfl
  have afterBlocks : after.blocks = [q.preheader, bankHeader q.row.graph, exitBlock] := rfl
  have entryDefs : p.preheader.defs = q.preheader.defs := by
    simp only [Block.defs, Plan.preheader, List.flatMap_def, emit_defs]
  have sameDigraph : before.digraph = after.digraph := by
    have sameSucc : before.succ = after.succ := by
      funext label
      simp only [Func.succ, Func.block?, beforeBlocks, afterBlocks, header]
      match label with
      | 0 | 1 | 2 | _ + 3 => rfl
    unfold Func.digraph
    rw [sameSucc]
    rfl
  have sameDefs (label : Nat) : before.defsOf label = after.defsOf label := by
    simp only [Func.defsOf, Func.block?, beforeBlocks, afterBlocks, header]
    match label with
    | 0 => exact entryDefs
    | 1 | 2 | _ + 3 => rfl
  have sameBlock {label : Nat} (nonzero : label ≠ 0) : before.block? label = after.block? label := by
    cases label with
    | zero => exact (nonzero rfl).elim
    | succ label => simp [Func.block?, beforeBlocks, afterBlocks, header]
  have sameUse {label : Nat} (nonzero : label ≠ 0) (pc : Nat) (reg : Reg) :
      before.okUse label pc reg = after.okUse label pc reg := by
    have sameDom (a b : Nat) : decide (before.Dominates a b) = decide (after.Dominates a b) :=
      decide_eq_decide.mpr (by simp only [Func.Dominates, sameDigraph])
    have len : before.blocks.length = after.blocks.length := rfl
    simp only [Func.okUse, sameBlock nonzero, sameDefs, sameDom, len]
  have sig : after.WellFormedSig := by
    refine ⟨wf.sig.1, wf.sig.2.1, ?_⟩
    have checked := wf.sig.2.2
    change (true && ((bankHeader p.row.graph).term.okIn 1 3 && true)) = true at checked
    change (true && ((bankHeader q.row.graph).term.okIn 1 3 && true)) = true
    rwa [header] at checked
  have assignment : after.SingleAssignment := by
    have old : before.SingleAssignment := wf.singleAssignment
    simpa only [Func.SingleAssignment, Func.allDefs, beforeBlocks, afterBlocks, List.flatMap_cons,
      entryDefs, header] using old
  refine ⟨sig, assignment, ?_, ?_⟩
  · have old : before.UsesDominated := wf.usesDominated
    change after.UsesDominated
    unfold Func.UsesDominated Func.usesDominated at old ⊢
    rw [List.all_eq_true] at old ⊢
    intro label within
    have bound : label < 3 := List.mem_range.mp within
    by_cases zero : label = 0
    · subst label
      rw [show after.block? 0 = some q.preheader from rfl, Bool.and_eq_true]
      have len : q.preheader.ops.length = entrySigs.length := emit_length q.flow
      constructor
      · rw [List.all_eq_true]
        intro j within
        have bound : j ≤ entrySigs.length := by
          rw [List.mem_range, len] at within
          exact Nat.le_of_lt within
        split
        · rename_i op found
          rw [List.all_eq_true]
          intro r used
          apply entry_okUse q bound
          simpa only [List.length_nil, Nat.zero_add] using emit_at_uses q.flow found r used
        · rfl
      · rw [List.all_eq_true]
        intro r used
        rw [len]
        have enough : (extend [] entrySigs).length ≤ entrySigs.length := by simp [extend_length]
        exact entry_okUse q (Nat.le_refl _) (bundle_uses q.entry enough r used)
    · have checked := old label (List.mem_range.mpr bound)
      have use : before.okUse label = after.okUse label := funext fun pc => funext (sameUse zero pc)
      rwa [sameBlock zero, use] at checked
  · have old : before.ArgsMatch := wf.argsMatch
    change after.ArgsMatch
    unfold Func.ArgsMatch Func.argsMatch at old ⊢
    rw [List.all_eq_true] at old ⊢
    intro block within
    rw [afterBlocks, List.mem_cons, List.mem_cons, List.mem_singleton] at within
    rcases within with rfl | rfl | rfl
    · change (((paramRegs arity arity).length == (q.entry.addresses.map (entryReg arity)).length) &&
        true) = true
      simp [paramRegs, entry_arity]
    · have checked := old (bankHeader p.row.graph) (by simp [beforeBlocks])
      have sameArity :
          (fun ta : Nat × List Reg => match before.block? ta.1 with
            | some b => b.params.length == ta.2.length
            | none => false) =
          (fun ta : Nat × List Reg => match after.block? ta.1 with
            | some b => b.params.length == ta.2.length
            | none => false) := by
        funext ⟨label, operands⟩
        match label with
        | 0 => rfl
        | n + 1 => rw [sameBlock (Nat.succ_ne_zero n)]
      rw [header] at checked
      exact (congrArg (bankHeader q.row.graph).term.args.all sameArity).symm.trans checked
    · rfl

theorem lowerChecked_mapCaptures (mapping : InputMap arity)
    {g : SourceWithEntry arity entrySigs sigs} {before : Checked.Phi.Targets}
    (accepted : lowerChecked g = some before) :
    ∃ after, lowerChecked (mapCaptures mapping g) = some after := by
  obtain ⟨p, recognized, wf, _⟩ := lowerChecked_sound accepted
  obtain ⟨column, ok, recognizes⟩ := recognize_mapCaptures mapping recognized
  let q : Plan arity entrySigs :=
    ⟨mapCaptureFlow mapping p.flow, ok, mapping.column p.entry, {p.row with entry := column}⟩
  have found : recognize (mapCaptures mapping g) = some q := recognizes
  have checked : q.lowerFunc.WellFormed := wellFormed_reentry p q rfl wf
  exact ⟨(q.rtl, Generic.lower (mapCaptures mapping g)), by
    simp only [lowerChecked, found, Option.bind_some, checked, ite_true]⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Proofs
