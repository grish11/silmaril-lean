module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement.Thms

/-! A self-loop lies strictly below an immediate return in result inclusion.
The inequality remains strict after versioning. -/

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement

open Silmaril.Elgot
open Comparison

private def spin : CFG Nat Nat Unit :=
  ⟨.term (.br 0 .unit), [(0, ⟨0, .term (.br 0 .unit)⟩)]⟩

private def returnUnit : CFG Nat Nat Unit :=
  ⟨.term (.br 1 .unit), []⟩

private def model : PairModel Unit Part Unit :=
  ⟨{ unit := ()
     pair := fun _ _ => ()
     inl := id
     inr := id
     unpair := fun _ => pure ((), ())
     split := fun _ => pure (.inl ())
     app := fun _ => pure
     abort := fun _ => Part.none },
   ⟨by intro left right; cases left; cases right; rfl⟩⟩

private theorem spinStep (m : PairModel Unit Part Unit) (store : Nat → Unit) :
    Cyclic.step m.val spin.blocks (0, m.val.unit, store) =
      Part.some (.inr (0, m.val.unit, upd store 0 m.val.unit)) := rfl

private theorem spinNoReturn (m : PairModel Unit Part Unit) {start exit : Transfer Nat Nat Unit}
    (finite : Silmaril.Elgot.Part.Runs (Cyclic.step m.val spin.blocks) start exit)
    (looping : start.1 = 0 ∧ start.2.1 = m.val.unit) : False := by
  induction finite with
  | @done start exit finished =>
    rcases start with ⟨label, value, store⟩
    obtain ⟨rfl, rfl⟩ := looping
    rw [spinStep] at finished
    simp at finished
  | @more start next exit continued _ ih =>
    rcases start with ⟨label, value, store⟩
    obtain ⟨rfl, rfl⟩ := looping
    rw [spinStep] at continued
    have nextTransfer : next = (0, m.val.unit, upd store 0 m.val.unit) := by simpa using continued
    subst next
    exact ih ⟨rfl, rfl⟩

private theorem spinObserve (m : PairModel Unit Part Unit) (store : Nat → Unit) :
    rtlObserve m spin store = Part.none := by
  apply Part.eq_none_iff.mpr
  intro result member
  change result ∈ Part.map obs (iter (Cyclic.step m.val spin.blocks) (0, m.val.unit, store)) at member
  obtain ⟨exit, returned, _⟩ := (Part.mem_map_iff obs).mp member
  exact spinNoReturn m ((Silmaril.Elgot.Part.mem_iter_iff _ _ exit).mp returned) ⟨rfl, rfl⟩

private theorem returnObserve (m : PairModel Unit Part Unit) (store : Nat → Unit) :
    rtlObserve m returnUnit store = Part.some (1, m.val.unit) := by
  have run : Cyclic.run m.val returnUnit store = Part.some (1, m.val.unit, store) :=
    Part.eq_some_iff.mpr ((Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr
      (.done (Part.mem_some _)))
  rw [rtlObserve, run]
  exact Part.map_some obs _

private noncomputable def spinClass : RTLClass Nat Nat Unit Part Unit := Quotient.mk _ spin

private noncomputable def returnClass : RTLClass Nat Nat Unit Part Unit := Quotient.mk _ returnUnit

private theorem spin_refines_return : rtlRefines spinClass returnClass := by
  intro m store
  change rtlObserve m spin store ≤ rtlObserve m returnUnit store
  rw [spinObserve]
  exact bot_le

private theorem return_does_not_refine_spin : ¬rtlRefines returnClass spinClass := by
  intro refines
  have included : rtlObserve model returnUnit (fun _ => ()) ≤ rtlObserve model spin (fun _ => ()) :=
    refines model (fun _ => ())
  rw [returnObserve, spinObserve] at included
  exact Part.notMem_none _ (included _ (Part.mem_some _))

example : ssaRefines (versionClass spinClass) (versionClass returnClass) ∧
    ¬ssaRefines (versionClass returnClass) (versionClass spinClass) :=
  ⟨(version_refines_iff _ _).mpr spin_refines_return,
    fun refines => return_does_not_refine_spin ((version_refines_iff _ _).mp refines)⟩

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement
