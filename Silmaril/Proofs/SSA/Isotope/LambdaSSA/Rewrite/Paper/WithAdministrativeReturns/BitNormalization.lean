module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Defs

/-! # Replay from the written source, with no equality premise -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.BitFragment
open Paper.WithCaseBind.BitQuery (signature Exits call call_typed)
open Paper.WithCaseBind.BitQuery.RequestTree (Tree inputSlots)
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (Candidate)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

set_option backward.isDefEq.respectTransparency false in
private theorem beta (label : Bool) :
    Eqv false [Bit, Bit] (call label operand) (call label (.var 0)) Exits := by
  let h : Tm.BranchValue [Bit, Bit] (.var 0 : Tm signature.Instr) Bit := .var (i := 0) rfl
  let l : Tm.HasType [Bit, Bit, Bit] (.var 0 : Tm signature.Instr) Bit := .var (i := 0) rfl
  let r : Tm.HasType [Bit, Bit, Bit] (.var 2 : Tm signature.Instr) Bit := .var (i := 2) rfl
  let left : ValueBranches [Bit, Bit, Bit] (.br 0 (.var 0) : Region signature.Instr) Exits :=
    .br (ℓ := 0) rfl (.var (i := 0) rfl)
  let right : ValueBranches [Bit, Bit, Bit] (.br 1 (.var 0) : Region signature.Instr) Exits :=
    .br (ℓ := 1) rfl (.var (i := 0) rfl)
  exact ofConstructorOperands false
    (Paper.WithConstructorCaseOperands.Step.caseCall (show signature.Instr from .ask label) (.left h l r) rfl left right).replay

set_option backward.isDefEq.respectTransparency false in
private theorem arm_replay (label wrapped : Bool) (i : Fin 2) :
    Eqv false [Bit, Bit] (.let₁ (arm wrapped i) (call label (.var 0)))
      (call label (.var i.val)) Exits := by
  let k : ValueBranches [Bit, Bit, Bit] (call label (.var 0)) Exits :=
    call_typed label (.var (i := 0) rfl)
  have direct : Eqv false [Bit, Bit] (.let₁ (.var i.val) (call label (.var 0)))
      (call label (.var i.val)) Exits :=
    .paper (.cfgEta (.native (.letValue (.var (slot_typed i)) k.hasType)))
  cases wrapped
  · exact direct
  · let read : Tm.HasType [Ty.unit, Bit, Bit] (.var (i.val + 1) : Tm signature.Instr) Bit :=
      .var (i := i.val + 1) (slot_typed i)
    let inner : HasType [Bit, Ty.unit, Bit, Bit] (call label (.var 0)) Exits :=
      (call_typed label (.var (i := 0) rfl)).hasType
    have move : Eqv false [Bit, Bit] (.let₁ (arm true i) (call label (.var 0)))
        (.let₁ .unit (.let₁ (.var (i.val + 1)) (call label (.var 0)))) Exits :=
      let₁_let₁ false (.unit : Tm.HasType [Bit, Bit] (.unit : Tm signature.Instr) Ty.unit) read k.hasType
    have drop : Eqv false [Bit, Bit] (.let₁ .unit (.let₁ (.var (i.val + 1)) (call label (.var 0))))
        (.let₁ (.var i.val) (call label (.var 0))) Exits :=
      .paper (.cfgEta (.native (.letValue .unit (.let₁ read inner))))
    exact move.trans (drop.trans direct)

private theorem written (p : Program) :
    p.tree.writtenRegion inputSlots =
      .case (.op (.ask p.testLabel) (.var 0))
        (call p.callLabel (.var p.leftSlot.val)) (call p.callLabel (.var p.rightSlot.val)) := by
  obtain ⟨testLabel, callLabel, l, r, nested⟩ := p
  fin_cases l <;> fin_cases r <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem replay (p : Program) :
    Eqv false [Bit] p.region (p.tree.writtenRegion inputSlots) Exits := by
  let hd := Tm.HasType.case (test_typed p.testLabel) (arm_typed p.nested p.leftSlot)
    (arm_typed p.nested p.rightSlot)
  let hk : ValueBranches [Bit, Bit] (call p.callLabel (.var 0)) Exits :=
    call_typed p.callLabel (.var (i := 0) rfl)
  rw [written]
  exact (Paper.Extension.Eqv.let₁ hd (beta p.callLabel)).trans
    ((let₁_case false (test_typed p.testLabel) (arm_typed p.nested p.leftSlot)
      (arm_typed p.nested p.rightSlot) hk.hasType).trans
      (.case (test_typed p.testLabel) (arm_replay p.callLabel p.nested p.leftSlot)
        (arm_replay p.callLabel p.nested p.rightSlot)))

theorem read_normal (p : Program) :
    (Candidate.readWithVariables ⟨p.tree.writtenRegion inputSlots, p.tree.written_typed inputSlots⟩ 4) =
      some p.tree := by
  obtain ⟨testLabel, callLabel, l, r, nested⟩ := p
  fin_cases l <;> fin_cases r <;> rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment
