module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs.Reindex

open Silmaril.Machine.RTL.SSA (Func)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg)
open Silmaril.SSA.RVSDG (Origin Tuple renameVertex)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

variable {arity : Nat}

private theorem argument_reindex (perm : InputPermutation arity) (i : Fin arity) :
    perm.port (argumentPort arity i) = argumentPort arity (perm i) := by
  simp only [InputPermutation.port, InputMap.port, InputPermutation.slot_argumentPort]

private theorem checkColumn_reindex (perm : InputPermutation arity) (width : Nat) (indices : List Nat) :
    checkColumn arity width (indices.map perm.index) = (checkColumn arity width indices).map perm.column := by
  induction width generalizing indices with
  | zero => cases indices <;> rfl
  | succ width ih =>
    cases indices with
    | nil => rfl
    | cons index rest =>
      by_cases h : index < arity
      · have valid := (perm ⟨index, h⟩).isLt
        simp only [List.map_cons, InputPermutation.index, renameVertex, dite_eq_left h,
          checkColumn, dite_eq_left valid, ih]
        cases checkColumn arity width rest <;>
          simp [InputPermutation.column, InputMap.column, mapColumn, mapOrigin, Tuple.map, argument_reindex, Option.map]
      · simp [InputPermutation.index, renameVertex, h, checkColumn]

theorem checkPlan_reindex (perm : InputPermutation arity) (spec : Spec) :
    checkPlan arity (spec.reindexInputs perm) =
      (checkPlan arity spec).map (fun p => p.reindexInputs perm) := by
  simp only [checkPlan, Spec.reindexInputs, checkColumn_reindex]
  cases checkColumn arity arity spec.entry with
  | none => rfl
  | some entry =>
    cases checkColumn arity arity spec.copies with
    | none => rfl
    | some copies =>
      cases checkFeedbackRow arity spec.updates with
      | none => rfl
      | some updates =>
        cases guardCheck : checkProducer updates spec.guardOrigin spec.guardDestination with
        | none => simp [guardCheck]
        | some guard =>
          cases rhsCheck : checkGuardOperand updates guard spec.guardRhs with
          | none => simp [guardCheck, rhsCheck]
          | some rhs =>
            by_cases exit : spec.exitSlot < arity
            · cases exitCheck : spec.exitOrigin.mapM (fun origin => checkProducer updates origin spec.exitSlot) <;>
                simp [guardCheck, rhsCheck, exit, exitCheck, Plan.reindexInputs]
            · simp [exit]

private theorem column_info {scope width : Nat} {raw : List Nat} {wires : ArgumentColumn scope width}
    (checked : checkColumn scope width raw = some wires) :
    raw.length = width ∧ ∀ i ∈ raw, i < scope := by
  induction width generalizing raw with
  | zero =>
    cases raw with
    | nil => simp
    | cons _ _ => cases checked
  | succ width ih =>
    cases raw with
    | nil => cases checked
    | cons index rest =>
      simp only [checkColumn] at checked
      split at checked
      · rename_i valid
        cases tail : checkColumn scope width rest with
        | none => simp [tail] at checked
        | some suffix =>
          obtain ⟨length, bounded⟩ := ih tail
          simpa [length, valid] using bounded
      · cases checked

private theorem checkPlan_entry {spec : Spec} {p : Plan arity}
    (ok : checkPlan arity spec = some p) :
    checkColumn arity arity spec.entry = some p.entry := by
  unfold checkPlan at ok
  rcases Option.bind_eq_some_iff.mp ok with ⟨entry, checked, rest⟩
  rcases Option.bind_eq_some_iff.mp rest with ⟨copies, _, rest⟩
  rcases Option.bind_eq_some_iff.mp rest with ⟨updates, _, rest⟩
  rcases Option.bind_eq_some_iff.mp rest with ⟨guard, _, rest⟩
  rcases Option.bind_eq_some_iff.mp rest with ⟨rhs, _, rest⟩
  split at rest
  · rcases Option.bind_eq_some_iff.mp rest with ⟨exitProducer, _, rest⟩
    cases Option.some.inj rest
    exact checked
  · cases rest

-- Only the preheader jump operands change. The control graph and all
-- definitions are the same, so the other blocks keep their use checks.
private theorem reindex_wellFormed {p q : Plan arity} {mapped : Spec}
    (mappedChecked : checkPlan arity mapped = some q)
    (perm : InputPermutation arity) (same : q = p.reindexInputs perm)
    (wf : (lowerBankFunc p.graph).WellFormed) :
    (lowerBankFunc q.graph).WellFormed := by
  subst q
  let before := lowerBankFunc p.graph
  let after := lowerBankFunc (p.reindexInputs perm).graph
  have afterEntry := checkPlan_entry mappedChecked
  have afterOps := checkColumn_registers afterEntry
  obtain ⟨afterLength, bounded⟩ := column_info afterEntry
  have sameDigraph : before.digraph = after.digraph := by
    have sameSucc : before.succ = after.succ := by
      funext label
      match label with
      | 0 | 1 | 2 | _ + 3 => rfl
    unfold Func.digraph
    rw [sameSucc]
    rfl
  have sameDefs (label : Nat) : before.defsOf label = after.defsOf label := by
    match label with
    | 0 | 1 | 2 | _ + 3 => rfl
  have sameDom (a b : Nat) : decide (before.Dominates a b) = decide (after.Dominates a b) :=
    decide_eq_decide.mpr (by simp only [Func.Dominates, sameDigraph])
  have sameUse (label pc : Nat) (reg : Reg) : before.okUse label pc reg = after.okUse label pc reg := by
    unfold Func.okUse
    simp only [sameDom, sameDefs]
    match label with
    | 0 | 1 | 2 | _ + 3 => rfl
  have sameBlock (label : Nat) (nonzero : label ≠ 0) : before.block? label = after.block? label := by
    cases label with
    | zero => exact (nonzero rfl).elim
    | succ label => rfl
  refine ⟨wf.sig, wf.singleAssignment, ?_, ?_⟩
  · have useEntry : ∀ r ∈ mapped.entry.map Reg.arg, after.okUse 0 0 r = true := by
      intro r member
      obtain ⟨i, occurs, rfl⟩ := List.mem_map.mp member
      have allowed := bounded i occurs
      have param : Reg.arg i ∈ paramRegs 0 arity := by
        apply List.mem_map.mpr
        exact ⟨i, by simpa using allowed, rfl⟩
      simp [after, Func.okUse, Func.block?, lowerBankFunc, bankPreheader, param]
    have oldUses := wf.usesDominated
    change before.UsesDominated at oldUses
    change after.UsesDominated
    unfold Func.UsesDominated Func.usesDominated at oldUses ⊢
    rw [List.all_eq_true] at oldUses ⊢
    intro label member
    have within : label < 3 := List.mem_range.mp member
    have labels : label = 0 ∨ label = 1 ∨ label = 2 := by omega
    rcases labels with rfl | rfl | rfl
    · change (emitColumn (p.reindexInputs perm).entry).all (after.okUse 0 0) = true
      rw [afterOps, List.all_eq_true]
      exact useEntry
    · have header := oldUses 1 (List.mem_range.mpr (show 1 < 3 by decide))
      have same : before.okUse 1 = after.okUse 1 := funext fun pc => funext (sameUse 1 pc)
      rw [sameBlock 1 (by decide), same] at header
      exact header
    · have exit := oldUses 2 (List.mem_range.mpr (show 2 < 3 by decide))
      have same : before.okUse 2 = after.okUse 2 := funext fun pc => funext (sameUse 2 pc)
      rw [sameBlock 2 (by decide), same] at exit
      exact exit
  · have oldArgs := wf.argsMatch
    change before.ArgsMatch at oldArgs
    change after.ArgsMatch
    unfold Func.ArgsMatch Func.argsMatch at oldArgs ⊢
    rw [List.all_eq_true] at oldArgs ⊢
    intro block member
    change block ∈ [bankPreheader (p.reindexInputs perm).graph, bankHeader p.graph, exitBlock] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · change (((paramRegs arity arity).length == (emitColumn (p.reindexInputs perm).entry).length) &&
        true) = true
      simp [afterOps, afterLength, paramRegs]
    · have header := oldArgs (bankHeader p.graph) (List.Mem.tail _ (List.Mem.head _))
      have sameArity :
          (fun ta : Nat × List Reg => match before.block? ta.1 with
            | some b => b.params.length == ta.2.length
            | none => false) =
          (fun ta : Nat × List Reg => match after.block? ta.1 with
            | some b => b.params.length == ta.2.length
            | none => false) := by
        funext ⟨label, operands⟩
        match label with
        | 0 | 1 | 2 | _ + 3 => rfl
      exact (congrArg (bankHeader p.graph).term.args.all sameArity).symm.trans header
    · rfl

theorem lowerChecked_reindex {spec : Spec} {targets : Checked.Phi.Targets}
    (perm : InputPermutation arity) (accepted : lowerChecked arity spec = some targets) :
    ∃ p, checkPlan arity spec = some p ∧
      lowerChecked arity (spec.reindexInputs perm) =
        some (lowerBank (p.reindexInputs perm).graph, Generic.lower (p.reindexInputs perm).graph) := by
  obtain ⟨p, checked, wf, rfl⟩ := (lowerChecked_eq_some_iff arity spec targets).mp accepted
  have rechecked := checkPlan_reindex perm spec
  rw [checked] at rechecked
  exact ⟨p, checked, (lowerChecked_eq_some_iff _ _ _).mpr
    ⟨p.reindexInputs perm, rechecked, reindex_wellFormed rechecked perm rfl wf, rfl⟩⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Proofs.Reindex
