module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native elimination of the guard already selected by a prior case -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.OpenReplay

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "E" => Paper.Extension.Eqv Seed

private theorem prunedArm_typed {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (g : GuardRequest L (n + 1))
    (test : Fin (n + 1)) (slots : Fin (n + 1) → Term signature.Instr (product X unit) Bit)
    (b : Bool) : ValueBranches [product X unit] (g.prunedArm test slots b) L :=
  prependEmits_typed g.emits (.let₁ (Term.snd (Φ := signature.Instr) X unit).elaborate.property
    (applyPacked_typed_exits (g.live test slots b).elaborate.property))

theorem pruned_typed {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (p : RepeatedGuard L n)
    (slots : Fin (n + 1) → Term signature.Instr X Bit) : ValueBranches [X] (p.prunedWith slots) L :=
  .case (emitPrefix p.emits (slots p.test)).elaborate.property
    (applyPacked_typed_exits (prunedArm_typed p.onFalse p.test (fun j => retainSlot (slots j)) false))
    (applyPacked_typed_exits (prunedArm_typed p.onTrue p.test (fun j => retainSlot (slots j)) true))

set_option backward.isDefEq.respectTransparency false in
private theorem known_arm_at {Γ L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (g : GuardRequest L (n + 1)) (test : Fin (n + 1)) (slots : Fin (n + 1) → ReplyFrame.Slot frame)
    (v : ReplyFrame.Value Γ frame) (b : Bool) (known : ((slots test).read v).1 = b) :
    let retained := fun j => retainSlot (A := unit) (slots j).term
    let packet := Tm.pair v.elaborate.val ((slots test).read v).2.val
    E Γ (((g.tree test).selectedWith retained).elaborate.val.substVars (Tm.singleSubst packet))
      ((g.prunedArm test retained b).substVars (Tm.singleSubst packet)) L := by
  let retained := fun j => retainSlot (A := unit) (slots j).term
  let payload := ((slots test).read v).2
  let incoming := ReplyFrame.Value.unit v payload
  let l := (g.live test retained false).elaborate
  let r := (g.live test retained true).elaborate
  have choose := framed_case_at (.retainUnit (slots test)) g.emits incoming l.property r.property
  have forwarded := forwardUnit_at g.emits v.elaborate.property payload.property
    (g.live test retained b).elaborate.property
  have tag : ((ReplyFrame.Slot.retainUnit (slots test)).read incoming).1 = b := known
  cases b
  · simp only [tag, Bool.false_eq_true, ↓reduceIte] at choose
    exact choose.trans forwarded.symm
  · simp only [tag, ↓reduceIte] at choose
    exact choose.trans forwarded.symm

set_option backward.isDefEq.respectTransparency false in
theorem repeated_eq_pruned {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : RepeatedGuard L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame) :
    E [X] (p.sourceWith (fun j => (slots j).term)).elaborate.val (p.prunedWith (fun j => (slots j).term)) L := by
  let retained := fun j => retainSlot (A := unit) (slots j).term
  let oldFalse := ((p.onFalse.tree p.test).selectedWith retained).elaborate
  let oldTrue := ((p.onTrue.tree p.test).selectedWith retained).elaborate
  let prunedFalse := prunedArm_typed p.onFalse p.test retained false
  let prunedTrue := prunedArm_typed p.onTrue p.test retained true
  apply frame_case_ext frame (p.sourceWith _).elaborate.property.hasType (pruned_typed p _).hasType
  intro Γ v
  have src := framed_case_at (slots p.test) p.emits v oldFalse.property oldTrue.property
  have dst := framed_case_at (slots p.test) p.emits v prunedFalse prunedTrue
  refine src.trans ((prependEmits_congr p.emits ?_).trans dst.symm)
  cases bit : ((slots p.test).read v).1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact known_arm_at p.onFalse p.test slots v false bit
  · simp only [↓reduceIte]
    exact known_arm_at p.onTrue p.test slots v true bit

theorem packed_eq_pruned {L : List (Ty Empty)} {n : Nat} (p : RepeatedGuard L n) :
    p.packedSource =
      Paper.Extension.Singleton.ofRegion Seed (pruned_typed p (readReply (n + 1))).packExits := by
  have native := repeated_eq_pruned p (ReplyFrame.standardSlots (n + 1))
  rw [standardSlots_term] at native
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (native.lsubstPost (p.sourceWith (readReply (n + 1))).elaborate.property
      (pruned_typed p (readReply (n + 1))) (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardReplay
