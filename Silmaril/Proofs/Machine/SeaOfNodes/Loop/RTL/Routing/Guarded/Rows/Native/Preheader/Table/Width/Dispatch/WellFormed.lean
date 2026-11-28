module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.WellFormed

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Proofs

open Silmaril.Machine.Graph (Digraph)
open Silmaril.Machine.RTL.SSA (Block Func Op Term Prog)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg)

variable {captures bank : Nat} {entrySigs sigs : List (List PortTy)}
variable (p : Source captures bank entrySigs sigs)

private def control (hasDispatch : Bool) : Digraph :=
  ⟨if hasDispatch then 4 else 3, fun label =>
    match label with
    | 0 => [1]
    | 1 => [if hasDispatch then 3 else 1, 2]
    | 2 => []
    | 3 => if hasDispatch then [1, 1] else []
    | _ + 4 => [], 0⟩

private theorem before_graph : (Width.lowerFunc p.primary).digraph = control false := by
  have succs : (Width.lowerFunc p.primary).succ = (control false).succ := by
    funext l
    match l with
    | 0 | 1 | 2 | 3 | _ + 4 => rfl
  unfold Func.digraph
  rw [succs]
  rfl

private theorem after_graph : (lowerFunc p).digraph = control true := by
  have succs : (lowerFunc p).succ = (control true).succ := by
    funext l
    match l with
    | 0 | 1 | 2 | 3 | _ + 4 => rfl
  unfold Func.digraph
  rw [succs]
  rfl

private theorem before_okUse (l pc : Nat) (r : Reg) (old : l < 3) :
    (Width.lowerFunc p.primary).okUse l pc r = (lowerFunc p).okUse l pc r := by
  let before := Width.lowerFunc p.primary
  let after := lowerFunc p
  have earlier (a : Nat) :
      (decide (a ≠ l) && decide (before.Dominates a l) && decide (r ∈ before.defsOf a)) =
      (decide (a ≠ l) && decide (after.Dominates a l) && decide (r ∈ after.defsOf a)) := by
    have sameDefs : before.defsOf a = after.defsOf a := by
      match a with
      | 0 | 1 | 2 | 3 | _ + 4 => rfl
    by_cases bound : a < 3
    · have sameDom : before.Dominates a l ↔ after.Dominates a l := by
        simp only [before, after, Func.Dominates, before_graph, after_graph]
        match a, l with
        | 0, 0 | 0, 1 | 0, 2 | 1, 0 | 1, 1 | 1, 2 | 2, 0 | 2, 1 | 2, 2 => decide
        | _ + 3, _ | _, _ + 3 => omega
      rw [sameDefs, decide_eq_decide.mpr sameDom]
    · have empty : before.defsOf a = [] := by
        match a with
        | 0 | 1 | 2 => omega
        | _ + 3 => rfl
      simp [← sameDefs, empty]
  have remote :
      ((List.range 3).any fun a => decide (a ≠ l) && decide (before.Dominates a l) &&
        decide (r ∈ before.defsOf a)) =
      ((List.range 4).any fun a => decide (a ≠ l) && decide (after.Dominates a l) &&
        decide (r ∈ after.defsOf a)) := by
    rw [show List.range 4 = List.range 3 ++ [3] by decide, List.any_append]
    simp only [show after.defsOf 3 = [] from rfl, List.not_mem_nil, decide_false,
      Bool.and_false, List.any_cons, List.any_nil, Bool.or_false]
    exact List.any_congr rfl earlier
  unfold Func.okUse
  match l with
  | 0 | 1 | 2 => exact congrArg (fun check => _ || check) remote
  | _ + 3 => omega

private theorem dispatch_okUse {r : Reg}
    (defined : r ∈ (Width.preheader p.primary).defs ∨ r ∈ (Width.header p.primary).defs) :
    (lowerFunc p).okUse 3 0 r = true := by
  rw [Func.okUse, Bool.or_eq_true]
  right
  apply List.any_eq_true.mpr
  have root : (lowerFunc p).Dominates 0 3 := by
    exact Digraph.Dominates.entry _ _
  have headerDom : (lowerFunc p).Dominates 1 3 := by
    rw [Func.Dominates, after_graph]
    decide
  rcases defined with entry | header
  · refine ⟨0, List.mem_range.mpr (show 0 < 4 by decide), ?_⟩
    have member : r ∈ (lowerFunc p).defsOf 0 := entry
    simp [root, member]
  · refine ⟨1, List.mem_range.mpr (show 1 < 4 by decide), ?_⟩
    have member : r ∈ (lowerFunc p).defsOf 1 := header
    simp [headerDom, member]

private theorem usesDominated (before : (Width.lowerFunc p.primary).UsesDominated) :
    (lowerFunc p).UsesDominated := by
  unfold Func.UsesDominated Func.usesDominated at before ⊢
  rw [List.all_eq_true] at before ⊢
  intro l within
  have bound : l < 4 := List.mem_range.mp within
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
  · have atDispatch : l = 3 := by omega
    subst l
    rw [show (lowerFunc p).block? 3 = some (dispatch p) from rfl]
    dsimp only
    rw [show (dispatch p).ops = [] from rfl, Bool.and_eq_true]
    refine ⟨rfl, List.all_eq_true.mpr ?_⟩
    intro r used
    apply dispatch_okUse p
    change r ∈ register p.selector.address :: (emitColumn (p.column true) ++ emitColumn (p.column false)) at used
    rcases List.mem_cons.mp used with rfl | operands
    · exact Width.Proofs.header_origin_defined p.primary p.selector
    · rcases List.mem_append.mp operands with onTrue | onFalse
      · exact Width.Proofs.header_column_defined p.primary (p.column true) onTrue
      · exact Width.Proofs.header_column_defined p.primary (p.column false) onFalse

theorem lowerFunc_wellFormed : (lowerFunc p).WellFormed := by
  have base := Width.Proofs.lowerFunc_wellFormed p.primary
  refine ⟨?_, ?_, usesDominated p base.usesDominated, ?_⟩
  · simp [Func.WellFormedSig, Func.block?, lowerFunc, Width.preheader, header, dispatch, exitBlock,
      Term.okIn, Term.successors, paramRegs]
  · exact base.singleAssignment
  · have entry := Width.Proofs.wires_length (p.primary.phiInputs .entry)
    have onTrue := Width.Proofs.wires_length (p.column true)
    have onFalse := Width.Proofs.wires_length (p.column false)
    simp [Func.ArgsMatch, Func.argsMatch, Func.block?, lowerFunc, Width.preheader, Width.header,
      header, dispatch, exitBlock, Term.args, paramRegs, emitColumn, entry, onTrue, onFalse]

theorem lowerChecked_of_accepted {old new : Nat} (mapping : InputMap old new)
    (p : Source old old entrySigs sigs) {left right : Checked.Phi.Targets}
    (primary : Table.lowerChecked (p.row true) = some left)
    (other : Table.lowerChecked (p.row false) = some right) :
    lowerChecked mapping p = some (lowerRTL (mapCaptures mapping p)) := by
  simp [lowerChecked, primary, other, lowerFunc_wellFormed]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Proofs
