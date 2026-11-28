module

import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Coproduct.Thms

section

namespace Silmaril.Isotope.LetCase.HandledTrace.Regression

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

private inductive Event : Type → Type where
  | mark (right : Bool) : Event Unit

private abbrev D := Ty.denote (fun _ : Empty => PUnit.{2})
private abbrev Slot := PUnit.{2}
private abbrev Packet := Slot ⊕ Slot
private abbrev unitTy : Ty Empty := .unit
private abbrev packetTy : Ty Empty := .coprod unitTy unitTy

local instance : HasTy Bool (Ty Empty) := ⟨fun _ => unitTy, fun _ => unitTy⟩

private def instructions : InstructionModel D Bool (Tree Event) :=
  ⟨fun right payload => vis (.mark right) (fun _ => pure payload)⟩

private def policy : Handler Bool Event :=
  fun _ current _ next => current = false ∧ next = true

private def slot : Interface instructions policy := ⟨unitTy⟩

private def arm : (right : Bool) → Program Bool unitTy packetTy
  | false => ⟨.inl (.op false (.bv 0)), .inl (.op .bv)⟩
  | true => ⟨.inr (.op true (.bv 0)), .inr (.op .bv)⟩

private def tag (right : Bool) (x : Slot) : Packet :=
  if right then .inr x else .inl x

private theorem run_arm (right : Bool) (x : Slot) :
    (arm right).run instructions x = vis (.mark right) (fun _ => ret (tag right x)) := by
  cases right
  · change (((pure x : Tree Event Slot) >>= fun a => vis (Event.mark false) (fun _ => pure a)) >>=
      fun a => pure (Sum.inl a : Packet)) = _
    simp only [pure_bind, vis_bind]
    rfl
  · change (((pure x : Tree Event Slot) >>= fun a => vis (Event.mark true) (fun _ => pure a)) >>=
      fun a => pure (Sum.inr a : Packet)) = _
    simp only [pure_bind, vis_bind]
    rfl

private theorem run_selected (right : Bool) (x : Slot) :
    ((arm false).desc (arm true)).run instructions (tag right x) =
      vis (.mark right) (fun _ => ret (tag right x)) := by
  have select := Program.run_desc (M := instructions) (arm false) (arm true) (tag right x)
  cases right
  · exact select.trans (run_arm false x)
  · exact select.trans (run_arm true x)

-- The payload type is identical on both sides. The tag determines the only
-- request, even when testing an unselected pending request before replay.
example (right : Bool) (x : Slot) :
    let tree := ((arm false).desc (arm true)).run instructions (tag right x)
    HandledTrace policy false tree (.exchange (.mark right) () (.result (tag right x))) ∧
      ¬ HandledTrace policy false tree (.request (.mark (!right))) := by
  dsimp only
  erw [run_selected]
  constructor
  · exact ⟨(hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _), ⟨true, ⟨rfl, rfl⟩, trivial⟩⟩
  · intro seen
    obtain ⟨sameType, sameEvent⟩ := (hasTrace_vis_request_iff _ _ _).mp seen.1
    have typeRefl : sameType = rfl := Subsingleton.elim _ _
    rw [typeRefl] at sameEvent
    have equalSide := Event.mark.inj sameEvent
    cases right <;> cases equalSide

-- The inverse order map uses the very same native case on representatives.
example :
    (Arrow.sumOrderIso slot slot (slot.sum slot)).symm
      (Arrow.ofProgram (arm false), Arrow.ofProgram (arm true)) =
        Arrow.ofProgram ((arm false).desc (arm true)) :=
  Arrow.desc_ofProgram (arm false) (arm true)

example : HasInitial (Interface instructions policy) := inferInstance

end Silmaril.Isotope.LetCase.HandledTrace.Regression

end
