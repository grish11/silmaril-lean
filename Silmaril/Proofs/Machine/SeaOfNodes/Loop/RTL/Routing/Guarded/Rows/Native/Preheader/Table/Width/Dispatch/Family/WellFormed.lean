module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.WellFormed
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Route

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Proofs

open Silmaril.Machine.Graph (Digraph)
open Silmaril.Machine.RTL.SSA (Block Func Term)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg)

variable {captures bank tests : Nat} {entrySigs sigs : List (List PortTy)}

private theorem chain_length (rows : Choices captures bank sigs tests) (first : Nat) :
    (rows.blocks first).length = tests + 1 := by
  induction rows generalizing first with
  | last _ => rfl
  | test _ _ _ ih => exact congrArg Nat.succ (ih (first + 1))

private theorem chain_defs (rows : Choices captures bank sigs tests) (first : Nat) :
    (rows.blocks first).flatMap Block.defs = [] := by
  induction rows generalizing first with
  | last _ => rfl
  | test _ _ _ ih => exact ih (first + 1)

private theorem column_length (column : Feedback captures bank sigs) :
    (emitColumn column).length = bank := by
  rw [emitColumn, List.length_map, Width.Proofs.wires_length]
  simp

private theorem chain_layout (g : Width.Source captures bank entrySigs sigs)
    (rows : Choices captures bank sigs tests) (first : Nat) (begins : 3 ≤ first)
    (block : Block Reg) (member : block ∈ rows.blocks first) :
    block.params = [] ∧ block.ops = [] ∧ block.term.okIn 1 (first + (tests + 1)) = true ∧
    (∀ r ∈ block.term.uses, r ∈ (Width.preheader g).defs ∨ r ∈ (Width.header g).defs) ∧
    ∀ arg ∈ block.term.args, (arg.1 = 1 ∧ arg.2.length = bank) ∨
      (3 ≤ arg.1 ∧ arg.1 < first + (tests + 1) ∧ arg.2 = []) := by
  induction rows generalizing first with
  | last column =>
    obtain rfl := List.mem_singleton.mp member
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · change (decide (1 < first + (0 + 1)) && true && true) = true
      simp only [Bool.and_true]
      exact decide_eq_true (show 1 < first + (0 + 1) by omega)
    · intro r used
      exact Width.Proofs.header_column_defined g column used
    · intro arg used
      obtain rfl := List.mem_singleton.mp used
      exact Or.inl ⟨rfl, column_length column⟩
  | @test n selector column tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · have inHeader : 1 < first + (n + 1 + 1) := by omega
        have inChain : first + 1 < first + (n + 1 + 1) := by omega
        simp [Term.okIn, Term.successors, inHeader, inChain]
      · intro r used
        change r ∈ register selector.address :: (emitColumn column ++ []) at used
        rcases List.mem_cons.mp used with rfl | uses
        · exact Width.Proofs.header_origin_defined g selector
        · rw [List.append_nil] at uses
          exact Width.Proofs.header_column_defined g column uses
      · intro arg used
        change arg ∈ [(1, emitColumn column), (first + 1, [])] at used
        rcases List.mem_cons.mp used with rfl | next
        · exact Or.inl ⟨rfl, column_length column⟩
        · obtain rfl := List.mem_singleton.mp next
          right
          change 3 ≤ first + 1 ∧ first + 1 < first + (n + 1 + 1) ∧ ([] : List Reg) = []
          exact ⟨by omega, by omega, rfl⟩
    · simpa only [Nat.add_assoc, Nat.add_comm 1 (n + 1)] using
        ih (first + 1) (by omega) later

private theorem header_dominates (g : Digraph) (entry : g.entry = 0) (first : g.succ 0 = [1])
    (b : Nat) (nonzero : b ≠ 0) : g.Dominates 1 b := by
  intro path proof
  cases path with
  | nil => cases proof.1
  | cons a tail =>
    have root : a = 0 := (Option.some.inj proof.1).trans entry
    subst a
    cases tail with
    | nil => exact (nonzero (Option.some.inj proof.2.1).symm).elim
    | cons next rest =>
      have edge := (List.isChain_cons_cons.mp proof.2.2).1
      have adjacent : next ∈ g.succ 0 := List.mem_of_mem_filter edge
      rw [first] at adjacent
      obtain rfl := List.mem_singleton.mp adjacent
      exact List.mem_cons_of_mem _ List.mem_cons_self

private theorem initial_dominance (g : Digraph) (entry : g.entry = 0) (first : g.succ 0 = [1])
    (size : 1 < g.size) (a l : Nat) (ha : a < 3) (hl : l < 3) :
    g.Dominates a l ↔ a = 0 ∨ a = l ∨ a = 1 ∧ l ≠ 0 := by
  constructor
  · intro h
    by_cases root : a = 0
    · exact Or.inl root
    by_cases same : a = l
    · exact Or.inr (Or.inl same)
    have nonzero : l ≠ 0 := fun eq => root (by
      rw [eq, ← entry] at h
      exact h.eq_entry.trans entry)
    by_cases head : a = 1
    · exact Or.inr (Or.inr ⟨head, nonzero⟩)
    have two : a = 2 := by omega
    have one : l = 1 := by omega
    subst a l
    have edge : g.Edge 0 1 := by simp [Digraph.Edge, Digraph.step, first, size]
    have path : g.Path g.entry 1 [0, 1] := ⟨by rw [entry]; rfl, rfl, .cons_cons edge (.singleton _)⟩
    have impossible := h _ path
    simp at impossible
  · rintro (rfl | rfl | ⟨rfl, nonzero⟩)
    · exact entry ▸ Digraph.Dominates.entry g l
    · exact Digraph.Dominates.refl g _
    · exact header_dominates g entry first l nonzero

variable (p : Source captures bank entrySigs sigs tests)

private theorem size : (lowerFunc p).blocks.length = 3 + (tests + 1) := by
  simp only [lowerFunc, List.length_append, List.length_cons, List.length_nil, chain_length]

private theorem chain_lookup (i : Nat) :
    (lowerFunc p).block? (3 + i) = (p.rows.blocks 3)[i]? := chain_block p i

private theorem chain_member {i : Nat} {b : Block Reg}
    (found : (lowerFunc p).block? (3 + i) = some b) : b ∈ p.rows.blocks 3 := by
  rw [chain_lookup] at found
  exact List.mem_of_getElem? found

private theorem before_okUse (l pc : Nat) (r : Reg) (old : l < 3) :
    (Width.lowerFunc p.primary).okUse l pc r = (lowerFunc p).okUse l pc r := by
  let before := Width.lowerFunc p.primary
  let after := lowerFunc p
  have preserved (a : Nat) (bound : a < 3) : before.defsOf a = after.defsOf a := by
    match a with
    | 0 | 1 | 2 => rfl
    | _ + 3 => omega
  have earlier (a : Nat) :
      (decide (a ≠ l) && decide (before.Dominates a l) && decide (r ∈ before.defsOf a)) =
      (decide (a ≠ l) && decide (after.Dominates a l) && decide (r ∈ after.defsOf a)) := by
    by_cases bound : a < 3
    · have beforeDom := initial_dominance before.digraph rfl rfl (by decide : 1 < 3) a l bound old
      have afterDom := initial_dominance after.digraph rfl rfl (by change 1 < (lowerFunc p).blocks.length; rw [size]; omega)
        a l bound old
      have same : before.Dominates a l ↔ after.Dominates a l := beforeDom.trans afterDom.symm
      rw [preserved a bound, decide_eq_decide.mpr same]
    · have oldEmpty : before.defsOf a = [] := by
        match a with
        | 0 | 1 | 2 => omega
        | _ + 3 => rfl
      have newEmpty : after.defsOf a = [] := by
        have address : a = 3 + (a - 3) := by omega
        change (lowerFunc p).defsOf a = []
        rw [address, Func.defsOf]
        split
        · rename_i b found
          obtain ⟨params, ops, _, _, _⟩ := chain_layout p.primary p.rows 3 (by decide) b (chain_member p found)
          simp [Block.defs, params, ops]
        · rfl
      simp [oldEmpty, newEmpty]
  have remote :
      ((List.range 3).any fun a => decide (a ≠ l) && decide (before.Dominates a l) &&
        decide (r ∈ before.defsOf a)) =
      ((List.range after.blocks.length).any fun a => decide (a ≠ l) && decide (after.Dominates a l) &&
        decide (r ∈ after.defsOf a)) := by
    have bounds : ∀ a : Nat, a ∈ List.range 3 → a ∈ List.range after.blocks.length := by
      intro a member
      have lt := List.mem_range.mp member
      rw [List.mem_range]
      change a < (lowerFunc p).blocks.length
      rw [size]
      omega
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨a, member, used⟩
      exact ⟨a, bounds a member, (earlier a).symm ▸ used⟩
    · rintro ⟨a, _, used⟩
      have usedOld := (earlier a).trans used
      have bound : a < 3 := by
        by_contra no
        have empty : before.defsOf a = [] := by
          match a with
          | 0 | 1 | 2 => omega
          | _ + 3 => rfl
        simp [empty] at usedOld
      exact ⟨a, List.mem_range.mpr bound, usedOld⟩
  unfold Func.okUse
  match l with
  | 0 | 1 | 2 => exact congrArg (fun check => _ || check) remote
  | _ + 3 => omega

private theorem chain_okUse {i : Nat} {r : Reg}
    (defined : r ∈ (Width.preheader p.primary).defs ∨ r ∈ (Width.header p.primary).defs) :
    (lowerFunc p).okUse (3 + i) 0 r = true := by
  rw [Func.okUse, Bool.or_eq_true]
  right
  apply List.any_eq_true.mpr
  have root : (lowerFunc p).Dominates 0 (3 + i) := Digraph.Dominates.entry _ _
  have fromHeader : (lowerFunc p).Dominates 1 (3 + i) :=
    header_dominates (lowerFunc p).digraph rfl rfl _ (by omega)
  rcases defined with entry | header
  · have member : r ∈ (lowerFunc p).defsOf 0 := entry
    exact ⟨0, List.mem_range.mpr (by rw [size]; omega), by simp [root, member, show 0 ≠ 3 + i by omega]⟩
  · have member : r ∈ (lowerFunc p).defsOf 1 := header
    exact ⟨1, List.mem_range.mpr (by rw [size]; omega), by
      have ne : 1 ≠ 3 + i := by omega
      simp [fromHeader, member, ne]⟩

private theorem usesDominated (before : (Width.lowerFunc p.primary).UsesDominated) :
    (lowerFunc p).UsesDominated := by
  unfold Func.UsesDominated Func.usesDominated at before ⊢
  rw [List.all_eq_true] at before ⊢
  intro l _
  by_cases earlier : l < 3
  · have old := before l (List.mem_range.mpr earlier)
    have uses : (Width.lowerFunc p.primary).okUse l = (lowerFunc p).okUse l :=
      funext fun pc => funext fun r => before_okUse p l pc r earlier
    rw [uses] at old
    match l with
    | 0 | 2 => exact old
    | 1 =>
      rw [show (Width.lowerFunc p.primary).block? 1 = some (Width.header p.primary) from rfl] at old
      rw [show (lowerFunc p).block? 1 = some (header p) from rfl]
      dsimp only at old ⊢
      rw [Bool.and_eq_true] at old ⊢
      refine ⟨old.1, List.all_eq_true.mpr ?_⟩
      intro r used
      apply List.all_eq_true.mp old.2
      change r ∈ [register p.primary.predicate.address, register p.primary.result.address] at used
      change r ∈ register p.primary.predicate.address ::
        (emitColumn (p.primary.phiInputs .backedge) ++ [register p.primary.result.address])
      rcases List.mem_cons.mp used with rfl | result
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ result)
    | _ + 3 => omega
  · have address : l = 3 + (l - 3) := by omega
    rw [address]
    split
    · rfl
    · rename_i b found
      obtain ⟨_, ops, _, sources, _⟩ := chain_layout p.primary p.rows 3 (by decide) b (chain_member p found)
      rw [ops, Bool.and_eq_true]
      exact ⟨rfl, List.all_eq_true.mpr fun r used => chain_okUse p (sources r used)⟩

private theorem signature : (lowerFunc p).WellFormedSig := by
  refine ⟨by change 0 < (lowerFunc p).blocks.length; rw [size]; omega, ?_, ?_⟩
  · change ((paramRegs 0 captures).length == captures) = true
    simp [paramRegs]
  · rw [List.all_eq_true]
    intro b member
    change b ∈ [Width.preheader p.primary, header p, exitBlock] ++ p.rows.blocks 3 at member
    rw [size]
    change b.term.okIn 1 (3 + (tests + 1)) = true
    rcases List.mem_append.mp member with fixed | chain
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
      have bounds : 1 < 3 + (tests + 1) ∧ 2 < 3 + (tests + 1) ∧ 3 < 3 + (tests + 1) := by omega
      rcases fixed with rfl | rfl | rfl <;>
        simp [Width.preheader, header, exitBlock, Term.okIn, Term.successors, bounds.1, bounds.2.1, bounds.2.2]
    · exact (chain_layout p.primary p.rows 3 (by decide) b chain).2.2.1

private theorem chain_target {label : Nat} (bound : 3 ≤ label) (inside : label < 3 + (tests + 1)) :
    ∃ b, (lowerFunc p).block? label = some b ∧ b.params = [] := by
  let i := label - 3
  have address : label = 3 + i := by dsimp [i]; omega
  have inList : i < (p.rows.blocks 3).length := by rw [chain_length]; dsimp [i]; omega
  have found : (lowerFunc p).block? label = some (p.rows.blocks 3)[i] := by
    rw [address, chain_lookup, List.getElem?_eq_getElem inList]
  exact ⟨_, found, (chain_layout p.primary p.rows 3 (by decide) _ (List.getElem_mem _)).1⟩

private theorem argsMatch : (lowerFunc p).ArgsMatch := by
  unfold Func.ArgsMatch Func.argsMatch
  rw [List.all_eq_true]
  intro b member
  change b ∈ [Width.preheader p.primary, header p, exitBlock] ++ p.rows.blocks 3 at member
  have headerFound : (lowerFunc p).block? 1 = some (header p) := rfl
  rcases List.mem_append.mp member with fixed | chain
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl | rfl
    · have width := Width.Proofs.wires_length (p.primary.phiInputs .entry)
      simp [Width.preheader, Term.args, headerFound, header, Width.header, paramRegs, width]
    · obtain ⟨b, atStart, empty⟩ := chain_target p (le_rfl : 3 ≤ 3) (by omega)
      have exit : (lowerFunc p).block? 2 = some exitBlock := rfl
      simp [header, Term.args, atStart, empty, exit, exitBlock]
    · rfl
  · rw [List.all_eq_true]
    intro arg used
    have targets := (chain_layout p.primary p.rows 3 (by decide) b chain).2.2.2.2 arg used
    rcases targets with ⟨target, len⟩ | ⟨lower, upper, empty⟩
    · simp [target, headerFound, header, Width.header, paramRegs, len]
    · obtain ⟨b, found, params⟩ := chain_target p lower upper
      simp [found, params, empty]

theorem lowerFunc_wellFormed : (lowerFunc p).WellFormed := by
  have base := Width.Proofs.lowerFunc_wellFormed p.primary
  refine ⟨signature p, ?_, usesDominated p base.usesDominated, argsMatch p⟩
  have original : (Width.lowerFunc p.primary).allDefs.Nodup := base.singleAssignment
  change (([Width.preheader p.primary, header p, exitBlock] ++ p.rows.blocks 3).flatMap Block.defs).Nodup
  rw [List.flatMap_append, chain_defs, List.append_nil]
  exact original

theorem lowerChecked_of_accepted {old new : Nat} (mapping : InputMap old new)
    (p : Source old old entrySigs sigs tests)
    (rows : ∀ slot, ∃ prior, Table.lowerChecked (p.row slot) = some prior) :
    lowerChecked mapping p = some (lowerRTL (mapCaptures mapping p)) := by
  simp [lowerChecked, (admitsRows_iff p).mpr rows, lowerFunc_wellFormed]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Proofs
