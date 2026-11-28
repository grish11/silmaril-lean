module

import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Distributivity.Thms

section

namespace Silmaril.Isotope.LetCase.HandledTrace.DistributivityRegression

open CategoryTheory CategoryTheory.Limits Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

private inductive Event : Type → Type where
  | mark (right : Bool) : Event Unit

private abbrev Slot := PUnit.{2}
private abbrev Bit := Slot ⊕ Slot
private abbrev Carry := Bit × Bit
private abbrev D := Ty.denote (fun _ : Empty => Slot)
private abbrev unitTy : Ty Empty := .unit
private abbrev bitTy : Ty Empty := .coprod unitTy unitTy
private abbrev carryTy : Ty Empty := .product bitTy bitTy

local instance : HasTy Bool (Ty Empty) := ⟨fun _ => unitTy, fun _ => unitTy⟩

private def instructions : InstructionModel D Bool (Tree Event) :=
  ⟨fun right a => vis (.mark right) (fun _ => pure a)⟩

private def policy : Handler Bool Event :=
  fun _ start _ finish => start = true ∧ finish = false

private def tag (right : Bool) : Bit :=
  if right then .inr PUnit.unit else .inl PUnit.unit

private def arm : (right : Bool) → Program Bool unitTy bitTy
  | false => ⟨.inl (.op false (.bv 0)), .inl (.op .bv)⟩
  | true => ⟨.inr (.op true (.bv 0)), .inr (.op .bv)⟩

private theorem run_arm (right : Bool) :
    (arm right).run instructions PUnit.unit = vis (.mark right) (fun _ => ret (tag right)) := by
  cases right
  · change (((pure PUnit.unit : Tree Event Slot) >>= fun a =>
      vis (Event.mark false) (fun _ => pure a)) >>= fun a => pure (Sum.inl a : Bit)) = _
    simp only [pure_bind, vis_bind]
    rfl
  · change (((pure PUnit.unit : Tree Event Slot) >>= fun a =>
      vis (Event.mark true) (fun _ => pure a)) >>= fun a => pure (Sum.inr a : Bit)) = _
    simp only [pure_bind, vis_bind]
    rfl

private theorem run_case (right : Bool) :
    ((arm false).desc (arm true)).run instructions (tag right) =
      vis (.mark right) (fun _ => ret (tag right)) := by
  have select := Program.run_desc (M := instructions) (arm false) (arm true) (tag right)
  cases right
  · exact select.trans (run_arm false)
  · exact select.trans (run_arm true)

private def leftBefore := ((arm false).desc (arm true)).whiskerLeft carryTy
private def leftAfter :=
  (Program.distribLeft carryTy unitTy unitTy).seq
    (((arm false).whiskerLeft carryTy).desc ((arm true).whiskerLeft carryTy))

private def rightBefore := ((arm false).desc (arm true)).whiskerRight carryTy
private def rightAfter :=
  (Program.distribRight unitTy unitTy carryTy).seq
    (((arm false).whiskerRight carryTy).desc ((arm true).whiskerRight carryTy))

private theorem run_leftBefore (fixed : Carry) (right : Bool) :
    leftBefore.run instructions (fixed, tag right) =
      vis (.mark right) (fun _ => ret (fixed, tag right)) := by
  refine (Program.run_whiskerLeft (M := instructions) (K := carryTy) ((arm false).desc (arm true)) fixed (tag right)).trans ?_
  erw [run_case, vis_bind]
  exact congrArg (vis (Event.mark right)) (funext fun _ => pure_bind _ _)

private theorem run_rightBefore (fixed : Carry) (right : Bool) :
    rightBefore.run instructions (tag right, fixed) =
      vis (.mark right) (fun _ => ret (tag right, fixed)) := by
  refine (Program.run_whiskerRight (M := instructions) (K := carryTy) ((arm false).desc (arm true)) (tag right) fixed).trans ?_
  erw [run_case, vis_bind]
  exact congrArg (vis (Event.mark right)) (funext fun _ => pure_bind _ _)

private def SelectedOnly {A : Type 1} (tree : Tree Event A) (state right : Bool) (result : A) : Prop :=
  HandledTrace policy state tree (.request (.mark right)) ∧
    (¬ HandledTrace policy state tree (.request (.mark (!right)))) ∧
    (∀ next, ¬ HandledTrace policy state tree (.exchange (.mark right) () (.request (.mark next)))) ∧
    (HandledTrace policy state tree (.exchange (.mark right) () (.result result)) ↔ state = true)

private theorem selectedOnly {A : Type 1} (state right : Bool) (result : A) :
    SelectedOnly (vis (.mark right) (fun _ => ret result)) state right result := by
  refine ⟨⟨hasTrace_vis_request _ _, trivial⟩, ?_, ?_, ?_⟩
  · intro seen
    obtain ⟨sameType, sameEvent⟩ := (hasTrace_vis_request_iff _ _ _).mp seen.1
    have typeRefl : sameType = rfl := Subsingleton.elim _ _
    rw [typeRefl] at sameEvent
    have equalSide := Event.mark.inj sameEvent
    cases right <;> cases equalSide
  · intro next seen
    obtain ⟨cont, impossible⟩ := (hasTrace_vis_exchange_iff _ _ _ _).mp seen.1
    rw [out_ret] at impossible
    cases Part.some_injective impossible
  · constructor
    · intro seen
      obtain ⟨_, admitted, _⟩ := seen.2
      exact admitted.1
    · rintro rfl
      exact ⟨(hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _), ⟨false, ⟨rfl, rfl⟩, trivial⟩⟩

-- Both tags carry the same unit value. The pending request is observable
-- even when the policy denies the exchange, and both retained bits survive.
example (fixed : Carry) (state right : Bool) :
    SelectedOnly (leftBefore.run instructions (fixed, tag right)) state right (fixed, tag right) ∧
    SelectedOnly (leftAfter.run instructions (fixed, tag right)) state right (fixed, tag right) := by
  have same : leftBefore.run instructions (fixed, tag right) = leftAfter.run instructions (fixed, tag right) :=
    Program.run_whiskerLeft_desc (arm false) (arm true) _
  erw [← same, run_leftBefore]
  exact ⟨selectedOnly state right _, selectedOnly state right _⟩

example (fixed : Carry) (state right : Bool) :
    SelectedOnly (rightBefore.run instructions (tag right, fixed)) state right (tag right, fixed) ∧
    SelectedOnly (rightAfter.run instructions (tag right, fixed)) state right (tag right, fixed) := by
  have same : rightBefore.run instructions (tag right, fixed) = rightAfter.run instructions (tag right, fixed) :=
    Program.run_whiskerRight_desc (arm false) (arm true) _
  erw [← same, run_rightBefore]
  exact ⟨selectedOnly state right _, selectedOnly state right _⟩

example : DistributivePremonoidalCategory (Interface instructions policy) := inferInstance

example (K : Interface instructions policy) :
    PreservesFiniteCoproducts (tensorLeft K) ∧ PreservesFiniteCoproducts (tensorRight K) :=
  ⟨inferInstance, inferInstance⟩

end Silmaril.Isotope.LetCase.HandledTrace.DistributivityRegression

end
