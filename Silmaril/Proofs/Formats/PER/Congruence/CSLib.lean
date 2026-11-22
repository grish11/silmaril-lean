module

public import Silmaril.Formats.PER.Congruence.CSLib.Defs

public section

namespace Silmaril.Proofs.Formats.PER.Congruence

open Silmaril.Formats

theorem support_context_lawful {α : Type} (C : PER.Constructors α) (R : PER α) (closed : C.Closed R) :
    @Cslib.LawfulCongruence _ R.supportSetoid.r ⟨⟩ (C.supportContexts R closed) := by
  let _ : Cslib.Congruence R.supportSetoid.r := ⟨⟩
  let _ : Cslib.HasContext {x // R.Dom x} := C.supportContexts R closed
  refine { refl := R.supportSetoid.iseqv.refl
           symm := fun _ _ => R.supportSetoid.iseqv.symm
           trans := fun _ _ _ => R.supportSetoid.iseqv.trans
           elim := ?_ }
  intro frame left right related
  change R.rel left.val right.val at related
  show R.rel (frame.fill closed left).val (frame.fill closed right).val
  refine closed frame.shape (frame.enabled left) (frame.enabled right) fun pos => ?_
  by_cases hole : pos = frame.hole
  · subst pos
    simpa only [frame.atHole] using related
  · rw [frame.fixed left right pos hole]
    exact (frame.args right pos).property

end Silmaril.Proofs.Formats.PER.Congruence
