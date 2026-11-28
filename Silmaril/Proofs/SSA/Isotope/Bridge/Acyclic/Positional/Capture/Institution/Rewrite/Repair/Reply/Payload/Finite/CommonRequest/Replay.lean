module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Factor
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Rename

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest

open Isotope.LetCase.LocallyNameless (Equiv HasType Tm)
open LambdaSSA.Region (packedExitType)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

private theorem request_before {L : List Sorts} {n k : Nat} {β : BoundCtx Sorts k}
    (req : Bool) (kept : Retained β n) (l r : Tree L (n + 1)) :
    Equiv false Γ₀ (β.snoc U)
      (Tm.let₁ (.op (.ask req) .unit)
        (answerCase (l.operand kept.bind) (r.operand kept.bind)).1.underBinder)
      (requestOperand req false (l.operand (kept.weaken U).bind) (r.operand (kept.weaken U).bind)).1
      (packedExitType L) := by
  have once := request_replay req true (l.operand (kept.weaken U).bind) (r.operand (kept.weaken U).bind)
    _ _ (.refl (l.operand (kept.weaken U).bind).2.toHasType) (.refl (r.operand (kept.weaken U).bind).2.toHasType)
  change Equiv false Γ₀ (β.snoc U) (requestOperand req true _ _).1 _ _ at once
  have left := operand_underBinder_proof l kept
  have right := operand_underBinder_proof r kept
  change Equiv false Γ₀ (β.snoc U) (Tm.let₁ (.op (.ask req) .unit)
    (.case (.bv 0) (l.operand (kept.weaken U).bind).1.underBinder
      (r.operand (kept.weaken U).bind).1.underBinder)) _ _ at once
  unfold answerCase
  change Equiv false Γ₀ (β.snoc U) (Tm.let₁ (.op (.ask req) .unit)
    ((Tm.case (.bv 0) (l.operand kept.bind).1.underBinder (r.operand kept.bind).1.underBinder).underBinder)) _ _
  rw [show ∀ a b : Tm Empty signature.Instr (k + 2),
      (Tm.case (.bv 0) a b).underBinder =
        .case (.bv 0) (a.rename (Tm.up (Tm.up Fin.succ))) (b.rename (Tm.up (Tm.up Fin.succ))) from fun _ _ => rfl,
    Tm.rename_underBinder, Tm.rename_underBinder]
  change Tm.rename (Tm.up Fin.succ) (l.operand kept.bind).1 = _ at left
  change Tm.rename (Tm.up Fin.succ) (r.operand kept.bind).1 = _ at right
  rw [left, right]
  exact once

theorem factor_source_proof {L : List Sorts} {n k : Nat} {β : BoundCtx Sorts k}
    (req : Bool) (arms : Arms L n) (slots : Retained β (n + 1)) (test : Fin (n + 1)) :
    Equiv false Γ₀ β ((Source.mk req false arms).operand slots test).1
      ((Source.mk req true arms).operand slots test).1 (packedExitType L) := by
  let kept := slots.without test
  let l := answerCase (arms.falseLeft.operand kept.bind) (arms.falseRight.operand kept.bind)
  let r := answerCase (arms.trueLeft.operand kept.bind) (arms.trueRight.operand kept.bind)
  let d := (slots.read test).2.toHasType
  have q : HasType signature.Instr Γ₀ β (.op (.ask req) .unit) Answer := .op .unit
  have factor := factor_proof d q l.2.toHasType r.2.toHasType
  exact (Equiv.case (.refl d)
    (request_before req kept arms.falseLeft arms.falseRight)
    (request_before req kept arms.trueLeft arms.trueRight)).symm.trans factor

theorem source_replay_proof {L : List Sorts} {n k : Nat} {β : BoundCtx Sorts k}
    (p : Source L n) (slots : Retained β (n + 1)) (test : Fin (n + 1)) :
    Equiv false Γ₀ β (p.operand slots test).1 (p.normal.render.operand slots test).1 (packedExitType L) := by
  obtain ⟨req, factored, arms⟩ := p
  let scope := ((slots.without test).weaken U).bind
  have normalize := Equiv.case (.refl (slots.read test).2.toHasType)
    (request_replay req false _ _ _ _ (arms.falseLeft.replay scope) (arms.falseRight.replay scope))
    (request_replay req false _ _ _ _ (arms.trueLeft.replay scope) (arms.trueRight.replay scope))
  cases factored
  · exact normalize
  · exact (factor_source_proof req arms slots test).symm.trans normalize

theorem derive_normal_proof (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1))
    (p q : Source (H :: L) n) (h : p.normal = q.normal) :
    Derivable false (equation H L test p q) := by
  have replay := source_replay_proof p (bitSlots _) test
  rw [h] at replay
  exact .let₁ (replay.trans (source_replay_proof q (bitSlots _) test).symm)
    (.refl ((program H L test p).body.render .base).encode.toLetCase.2.toHasType)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest
