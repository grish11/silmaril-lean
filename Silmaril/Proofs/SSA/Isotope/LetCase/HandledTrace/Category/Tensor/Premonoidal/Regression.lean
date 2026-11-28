module

import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Premonoidal.Thms

section

namespace Silmaril.Isotope.LetCase.HandledTrace.PremonoidalRegression

open CategoryTheory LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree
open scoped PremonoidalCategory

private inductive Event : Type → Type where
  | ask : Event Bool

private abbrev Slot := PUnit.{2}
private abbrev Bit := Slot ⊕ Slot
private abbrev D := Ty.denote (fun _ : Empty => Slot)
private abbrev unitTy : Ty Empty := .unit
private abbrev bitTy : Ty Empty := .coprod unitTy unitTy
private abbrev pairTy : Ty Empty := .product bitTy bitTy

local instance : HasTy Unit (Ty Empty) := ⟨fun _ => unitTy, fun _ => bitTy⟩
local instance : HasEff Unit Bool := ⟨fun _ => true⟩

private def replyTag (reply : Bool) : Bit :=
  if reply then .inr PUnit.unit else .inl PUnit.unit

private def instructions : InstructionModel D Unit (Tree Event) :=
  ⟨fun _ _ => vis .ask (fun reply => pure (replyTag reply))⟩

private def policy : Handler Bool Event
  | ⟨_, .ask⟩, start, reply, finish => start = true ∧ reply = true ∧ finish = false

private def bit : Interface instructions policy := ⟨bitTy⟩
private def token : Interface instructions policy := ⟨unitTy⟩

private def duplicate : Program Unit bitTy pairTy :=
  ⟨.pair (.bv 0) (.bv 0), .pair .bv .bv⟩

private def request : Program Unit unitTy bitTy :=
  ⟨.op () (.bv 0), .op .bv⟩

private theorem compatible : instructions.RespectsPure (ε := Bool) := by
  intro opcode pureOpcode
  change true = false at pureOpcode
  cases pureOpcode

private theorem duplicatePure : Pure (⊥ : Bool) duplicate.1 := .pair .bv .bv

private theorem duplicateRun (payload : Bit) :
    duplicate.run instructions payload = (pure (payload, payload) : Tree Event (Bit × Bit)) := by
  change ((pure payload : Tree Event Bit) >>= fun a =>
    (pure payload : Tree Event Bit) >>= fun b => pure (a, b)) = _
  simp only [pure_bind]

private theorem requestRun :
    request.run instructions PUnit.unit = vis .ask (fun b => pure (replyTag b)) := by
  change ((pure PUnit.unit : Tree Event Slot) >>= fun _ =>
    vis Event.ask (fun b => pure (replyTag b))) = _
  rw [pure_bind]

private theorem leftRun (payload : Bit) :
    (duplicate.leftTensor request).run instructions (payload, PUnit.unit) =
      vis .ask (fun reply => ret ((payload, payload), replyTag reply)) := by
  let input := (ProductModel.productEquiv (D := D) bitTy unitTy).symm (payload, PUnit.unit)
  let kept : D pairTy := (payload, payload)
  let mid := (ProductModel.productEquiv (D := D) pairTy unitTy).symm (kept, PUnit.unit)
  have first : (duplicate.whiskerRight unitTy).run instructions input = pure mid := by
    dsimp only [input, mid]
    erw [Program.run_whiskerRight, duplicateRun]
    exact pure_bind _ _
  refine (Program.run_seq (duplicate.whiskerRight unitTy) (request.whiskerLeft pairTy) input).trans ?_
  rw [first]
  refine (pure_bind _ _).trans ?_
  refine (Program.run_whiskerLeft (K := pairTy) (M := instructions) request kept PUnit.unit).trans ?_
  erw [requestRun, vis_bind]
  exact congrArg (vis Event.ask) (funext fun _ => pure_bind _ _)

-- The same retained payload and typed reply are observed in both written
-- orders. The reply is denied when the original handler state is false.
example (payload : Bit) (state : Bool) :
    let trace : Trace Event ((Bit × Bit) × Bit) :=
      .exchange .ask true (.result ((payload, payload), replyTag true))
    (HandledTrace policy state ((duplicate.leftTensor request).run instructions (payload, PUnit.unit)) trace ∧
     HandledTrace policy state ((duplicate.rightTensor request).run instructions (payload, PUnit.unit)) trace) ↔
      state = true := by
  dsimp only
  have same := Program.run_leftTensor_eq_rightTensor_of_left_pure request
    (Program.pureRun_of_pure compatible duplicatePure)
    (show D (.product bitTy unitTy) from (payload, PUnit.unit))
  erw [← same, leftRun]
  constructor
  · rintro ⟨seen, _⟩
    obtain ⟨_, admitted, _⟩ := seen.2
    exact admitted.1
  · rintro rfl
    have seen : HandledTrace policy true (vis .ask (fun b => ret ((payload, payload), replyTag b)))
        (.exchange .ask true (.result ((payload, payload), replyTag true))) :=
      ⟨(hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _), ⟨false, ⟨rfl, rfl, rfl⟩, trivial⟩⟩
    exact ⟨seen, seen⟩

example :
    Arrow.ofProgram (A := bit) (B := bit.tensor bit) duplicate ⋉
      Arrow.ofProgram (A := token) (B := bit) request =
    Arrow.ofProgram (A := bit) (B := bit.tensor bit) duplicate ⋊
      Arrow.ofProgram (A := token) (B := bit) request :=
  (Arrow.isCentral_of_pure (A := bit) (B := bit.tensor bit) compatible duplicatePure).1 _

end Silmaril.Isotope.LetCase.HandledTrace.PremonoidalRegression

end
