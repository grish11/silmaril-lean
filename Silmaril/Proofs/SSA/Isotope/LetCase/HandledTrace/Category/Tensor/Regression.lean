module

import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Tensor.Thms

section

namespace Silmaril.Isotope.LetCase.HandledTrace.TensorRegression

open CategoryTheory Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

private inductive Event : Type → Type where
  | ask : Event Unit

private abbrev Slot := PUnit.{2}
private abbrev Bit := Slot ⊕ Slot
private abbrev D := Ty.denote (fun _ : Empty => Slot)
private abbrev unitTy : Ty Empty := .unit
private abbrev bitTy : Ty Empty := .coprod unitTy unitTy

local instance : HasTy Bool (Ty Empty) := ⟨fun _ => unitTy, fun _ => unitTy⟩

private def instructions : InstructionModel D Bool (Tree Event) :=
  ⟨fun complete a => vis .ask (fun _ => if complete then pure a else diverge)⟩

private def policy : Handler Bool Event :=
  fun _ start _ finish => start = true ∧ finish = false

private def active : Interface instructions policy := ⟨unitTy⟩
private def idle : Interface instructions policy := ⟨bitTy⟩

private def call (complete : Bool) : Program Bool unitTy unitTy :=
  ⟨.op complete (.bv 0), .op .bv⟩

private def arrow (complete : Bool) : active ⟶ active :=
  Arrow.ofProgram (call complete)

private def retained : Bit := .inr PUnit.unit
private def witness : Trace Event Slot := .exchange .ask () (.result PUnit.unit)

private theorem run_call (complete : Bool) (a : Slot) :
    (call complete).run instructions a = vis .ask (fun _ => if complete then pure a else diverge) := by
  change ((pure a : Tree Event Slot) >>= fun b =>
    vis Event.ask (fun _ => if complete then pure b else diverge)) = _
  rw [pure_bind]

private theorem refines : arrow false ≤ arrow true := by
  apply Arrow.ofProgram_le_ofProgram.mpr
  intro a state
  erw [run_call, run_call]
  have incl : TraceLE (vis Event.ask (fun _ => diverge)) (vis Event.ask (fun _ => pure a)) :=
    TraceLE.vis Event.ask (fun _ => traceLE_diverge _)
  exact fun trace seen => ⟨incl trace seen.1, seen.2⟩

private theorem complete : HandledTrace policy true ((call true).run instructions PUnit.unit) witness := by
  erw [run_call]
  exact ⟨(hasTrace_vis_exchange_iff _ _ _ _).mpr (out_ret _), ⟨false, ⟨rfl, rfl⟩, trivial⟩⟩

private theorem pause_absent {T : Type 1} (tag : Slot → T) :
    ¬ HandledTrace policy true ((call false).run instructions PUnit.unit >>= fun a => pure (tag a))
      (witness.map tag) := by
  intro seen
  have observed := seen.1
  erw [run_call] at observed
  change HasTrace (vis Event.ask (fun _ => (diverge : Tree Event Slot)) >>= fun a => pure (tag a))
    (.exchange .ask () (.result (tag PUnit.unit))) at observed
  simp only [vis_bind, diverge_bind, hasTrace_vis_exchange_iff, hasTrace_diverge_iff] at observed
  cases observed

-- Both retained tags are observed. Changing only the initial state can
-- deny that same exchange, even though the request remains pending.
example (fixed : Bit) (state : Bool) :
    let prod := ProductModel.productEquiv (D := D) bitTy unitTy
    HandledTrace policy state (((call true).whiskerLeft bitTy).run instructions
      (prod.symm (fixed, PUnit.unit))) (witness.map fun a => prod.symm (fixed, a)) ↔ state = true := by
  dsimp only
  constructor
  · intro seen
    obtain ⟨_, admitted, _⟩ := seen.2
    exact admitted.1
  · rintro rfl
    exact (Program.handledTrace_whiskerLeft_iff (M := instructions) (K := bitTy)
      (call true) fixed PUnit.unit true _).mpr ⟨witness, complete, rfl⟩

-- The same exchange returns the right-tagged retained input on the left,
-- from the original state (the other state would deny the reply).
example : (tensorLeft idle).map (arrow false) < (tensorLeft idle).map (arrow true) := by
  apply lt_of_le_not_ge (tensorLeft_enriched idle refines)
  intro reverse
  have compares : Program.Refines instructions policy ((call true).whiskerLeft bitTy)
      ((call false).whiskerLeft bitTy) := Arrow.ofProgram_le_ofProgram.mp reverse
  let tag (a : Slot) : Bit × Slot := (retained, a)
  have seen := (Program.handledTrace_whiskerLeft_iff (M := instructions) (policy := policy) (K := bitTy)
    (call true) retained PUnit.unit true (witness.map tag)).mpr ⟨witness, complete, rfl⟩
  have impossible := compares ((ProductModel.productEquiv (D := D) bitTy unitTy).symm (retained, PUnit.unit)) true (witness.map tag) seen
  erw [Program.run_whiskerLeft] at impossible
  exact pause_absent tag impossible

example : (tensorRight idle).map (arrow false) < (tensorRight idle).map (arrow true) := by
  apply lt_of_le_not_ge (tensorRight_enriched idle refines)
  intro reverse
  have compares : Program.Refines instructions policy ((call true).whiskerRight bitTy)
      ((call false).whiskerRight bitTy) := Arrow.ofProgram_le_ofProgram.mp reverse
  let tag (a : Slot) : Slot × Bit := (a, retained)
  have seen := (Program.handledTrace_whiskerRight_iff (M := instructions) (policy := policy) (K := bitTy)
    (call true) PUnit.unit retained true (witness.map tag)).mpr ⟨witness, complete, rfl⟩
  have impossible := compares ((ProductModel.productEquiv (D := D) unitTy bitTy).symm (PUnit.unit, retained)) true (witness.map tag) seen
  erw [Program.run_whiskerRight] at impossible
  exact pause_absent tag impossible

end Silmaril.Isotope.LetCase.HandledTrace.TensorRegression

end
