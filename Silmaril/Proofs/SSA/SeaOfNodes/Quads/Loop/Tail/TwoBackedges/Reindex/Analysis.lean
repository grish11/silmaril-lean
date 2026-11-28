module

public import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Native
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Proofs

open SeaOfNodes.Diamond (Model ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact tupleFacts)
open SeaOfNodes.Loop.SCCP (BankFacts BankDecidableEq bankTuple bankTuple_tupleFacts)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation pull pull_get)
open RVSDG (Tuple)
open Join (Block)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {old new : List (ValueSort Data)} {out : ValueSort Data}
variable (order : Registers old new) (m : Model.{u, v, w} Op)

theorem blockFacts_pull (block : Block Op old) (input : Tuple (Fact m.value) (dataPorts new)) :
    pull order (SCCP.blockFacts m (block.map (quad order)) input) =
      SCCP.blockFacts m block (pull order input) := by
  simp only [SCCP.blockFacts_fold]
  induction block generalizing input with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    apply congrArg (fun bank => rest.foldl (fun bank q => SCCP.quadFacts m q bank) bank)
    simp only [SCCP.quadFacts, quad, read_renamed]
    exact pull_write (F := Fact m.value) order q.dest _ input

private theorem tupleFacts_bankTuple {value : Data → Type w}
    {ports : List (SeaOfNodes.Diamond.Ty Data)} (bank : BankFacts value ports) :
    tupleFacts (bankTuple bank) = bank := by
  induction ports with
  | nil => exact funext fun i => i.elim0
  | cons _ rest ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun k => bank k.succ)) j

theorem pull_push {F : SeaOfNodes.Diamond.Ty Data → Type w}
    (input : Tuple F (dataPorts old)) : pull order (push order input) = input := by
  apply tuple_ext
  intro t p
  simp [push, pull_get, Permutation.symm]

private theorem push_pull {F : SeaOfNodes.Diamond.Ty Data → Type w}
    (input : Tuple F (dataPorts new)) : push order (pull order input) = input := by
  apply tuple_ext
  intro t p
  simp [push, pull_get, Permutation.symm]

private theorem bankTuple_order {value : Data → Type w}
    {ports : List (SeaOfNodes.Diamond.Ty Data)} (a b : BankFacts value ports) :
    a ≤ b ↔ ∀ {t} (p : RVSDG.Port ports t), (bankTuple a).get p ≤ (bankTuple b).get p := by
  constructor
  · intro h t p
    induction p with
    | head => exact h 0
    | tail p ih => exact ih _ _ (fun i => h i.succ)
  · induction ports with
    | nil => intro _ i; exact i.elim0
    | cons head tail ih =>
      intro h i
      refine Fin.cases (h .head) (fun j => ?_) i
      exact ih _ _ (fun p => h (.tail p)) j

private def bankPush {value : Data → Type w} (bank : BankFacts value (dataPorts old)) :
    BankFacts value (dataPorts new) :=
  tupleFacts (push order (bankTuple bank))

private theorem bankPush_le_iff {value : Data → Type w} (a b : BankFacts value (dataPorts old)) :
    bankPush order a ≤ bankPush order b ↔ a ≤ b := by
  simp only [bankTuple_order, bankPush, bankTuple_tupleFacts, push, pull_get, Permutation.symm]
  constructor
  · intro h t p
    simpa using h (order t p)
  · intro h t p
    exact h ((order t).symm p)

private theorem bankPush_cancel {value : Data → Type w} (bank : BankFacts value (dataPorts new)) :
    bankPush order (bankPush order.symm bank) = bank := by
  simp only [bankPush, bankTuple_tupleFacts, show push order.symm = @pull _ _ _ _ order from rfl,
    push_pull, tupleFacts_bankTuple]

private theorem phiFacts_push {value : Data → Type w}
    [BankDecidableEq value (dataPorts old)] [BankDecidableEq value (dataPorts new)]
    (marks : SCCP.Marked) (column : Incoming → BankFacts value (dataPorts old)) :
    SCCP.phiFacts marks (fun edge => bankPush order (column edge)) =
      bankPush order (SCCP.phiFacts marks column) := by
  apply le_antisymm
  · apply (SCCP.phiFacts_le_iff _ _ _).2
    intro edge marked
    exact (bankPush_le_iff order _ _).2 ((SCCP.phiFacts_le_iff _ _ _).1 le_rfl edge marked)
  · let upper := SCCP.phiFacts marks (fun edge => bankPush order (column edge))
    have h : SCCP.phiFacts marks column ≤ bankPush order.symm upper :=
      (SCCP.phiFacts_le_iff _ _ _).2 fun edge marked =>
        (bankPush_le_iff order _ _).1 (by
          rw [bankPush_cancel]
          exact (SCCP.phiFacts_le_iff marks (fun edge => bankPush order (column edge)) upper).1 le_rfl edge marked)
    have moved := (bankPush_le_iff order _ _).2 h
    rwa [bankPush_cancel] at moved

variable (p : Program Op old out)
variable [BankDecidableEq m.value (dataPorts old)] [BankDecidableEq m.value (dataPorts new)]
variable (input : Tuple (Fact m.value) (dataPorts old))

theorem transfer_assignment (state : SCCP.State m.value old out) :
    SCCP.transfer m (program order p) (push order input) (assignment order state) =
      assignment order (SCCP.transfer m p input state) := by
  let current := SCCP.blockFacts m p.header (bankTuple state.2.1)
  let newer := SCCP.blockFacts m (program order p).header (bankTuple (assignment order state).2.1)
  have header : pull order newer = current := by
    simp only [newer, current, program, assignment, bankTuple_tupleFacts, blockFacts_pull, pull_push]
  have block_push (block : Block Op old) (bank : Tuple (Fact m.value) (dataPorts new)) :
      SCCP.blockFacts m (block.map (quad order)) bank =
        push order (SCCP.blockFacts m block (pull order bank)) :=
    (push_pull order _).symm.trans (congrArg (push order) (blockFacts_pull order m block bank))
  have columns : SCCP.columns m (program order p) (push order input) newer =
      fun edge => bankPush order (SCCP.columns m p input current edge) := by
    funext edge
    cases edge with
    | entry => simp only [SCCP.columns, bankPush, bankTuple_tupleFacts, program, block_push, pull_push]
    | feedback side => simp only [SCCP.columns, bankPush, bankTuple_tupleFacts, program, block_push, header]
  have phi := (phiFacts_push order state.1 (SCCP.columns m p input current))
  rw [← columns] at phi
  have test := congrArg (fun bank : Tuple (Fact m.value) (dataPorts old) => bank.get p.again) header
  have select := congrArg (fun bank : Tuple (Fact m.value) (dataPorts old) => bank.get p.select) header
  have result := congrArg (fun bank : Tuple (Fact m.value) (dataPorts old) => bank.get p.result) header
  simp only [pull_get] at test select result
  change (insert (SCCP.incomingIndex .entry) (if SCCP.incomingIndex .entry ∈ state.1 then
      SCCP.successors (newer.get (order _ p.again)) (newer.get (order _ p.select)) else ∅),
    SCCP.phiFacts state.1 (SCCP.columns m (program order p) (push order input) newer),
      SCCP.gate state.1 SCCP.exitIndex (newer.get (order _ p.result))) =
    (insert (SCCP.incomingIndex .entry) (if SCCP.incomingIndex .entry ∈ state.1 then
      SCCP.successors (current.get p.again) (current.get p.select) else ∅),
    bankPush order (SCCP.phiFacts state.1 (SCCP.columns m p input current)),
      SCCP.gate state.1 SCCP.exitIndex (current.get p.result))
  rw [test, select, phi, result]

theorem solve_assignment :
    SCCP.solve m (program order p) (push order input) = assignment order (SCCP.solve m p input) := by
  let previous := SCCP.solve m p input
  let renamed := SCCP.solve m (program order p) (push order input)
  have fixed : SCCP.transfer m (program order p) (push order input) (assignment order previous) =
      assignment order previous := by
    rw [transfer_assignment, SCCP.solve_fixed]
  have order_mono : ∀ (a b : SCCP.State m.value old out), a ≤ b ↔ assignment order a ≤ assignment order b := by
    intro a b
    change (a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2) ↔
      (a.1 ≤ b.1 ∧ bankPush order a.2.1 ≤ bankPush order b.2.1 ∧ a.2.2 ≤ b.2.2)
    rw [bankPush_le_iff]
  have cancel (a : SCCP.State m.value new out) : assignment order (assignment order.symm a) = a := by
    obtain ⟨marks, bank, answer⟩ := a
    exact congrArg (fun b => (marks, b, answer)) (bankPush_cancel order bank)
  have source_fixed : SCCP.transfer m p input (assignment order.symm renamed) = assignment order.symm renamed := by
    apply le_antisymm
    · apply (order_mono _ _).2
      rw [← transfer_assignment, cancel, SCCP.solve_fixed]
    · apply (order_mono _ _).2
      rw [← transfer_assignment, cancel, SCCP.solve_fixed]
  apply le_antisymm
  · exact (SCCP.solve_isLeast m (program order p) (push order input)).2 fixed
  · have h := (order_mono _ _).1 ((SCCP.solve_isLeast m p input).2 source_fixed)
    rwa [cancel] at h

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Proofs
