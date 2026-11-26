module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement.Plugging.Thms
import Mathlib.Data.Nat.Pairing

/-! Both source graphs return the same label and packet in every model.
A single register assignment becomes observable when the next body reads
the carried store. -/

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement

open Comparison

private def keepRegister : CFG Unit Nat Unit :=
  ⟨.term (.br 0 .unit), []⟩

private def clearRegister : CFG Unit Nat Unit :=
  ⟨.let1 () (.val .unit) (.term (.br 0 .unit)), []⟩

private def model : PairModel Unit Part Nat :=
  ⟨{ unit := 0
     pair := Nat.pair
     inl := id
     inr := Nat.succ
     unpair n := pure (Nat.unpair n)
     split n := pure (.inl n)
     app _ := pure
     abort _ := Part.none },
   ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩⟩

private def readRegister (m : Model Unit Part Nat) (transfer : Transfer Unit Nat Nat) :
    Part (Nat × Nat) :=
  (Body.term (.br 1 (.var ())) : Body Unit Nat Unit).evalJump m transfer.2.2

private theorem keepRun (m : PairModel Unit Part Nat) (store : Unit → Nat) :
    Cyclic.run m.val keepRegister store = Part.some (0, m.val.unit, store) := by
  rw [Cyclic.run_eq_forward m.val keepRegister trivial]
  rfl

private theorem clearRun (m : PairModel Unit Part Nat) (store : Unit → Nat) :
    Cyclic.run m.val clearRegister store = Part.some (0, m.val.unit, upd store () m.val.unit) := by
  rw [Cyclic.run_eq_forward m.val clearRegister trivial]
  simp [clearRegister, CFG.run, Body.exec, Term.exec, Op.eval, Val.eval, jump]

private theorem sameClass : (Quotient.mk _ keepRegister : RTLClass Unit Nat Unit Part Nat) =
    Quotient.mk _ clearRegister := by
  refine Quotient.sound fun m store => ?_
  rw [rtlObserve, rtlObserve, keepRun, clearRun]
  rfl

private def initial : Unit → Nat := fun _ => 1

private theorem keepPlug :
    plugRTLWithStore model keepRegister initial (readRegister model.val) = Part.some (1, 1) := by
  rw [plugRTLWithStore, keepRun]
  simp [readRegister, Body.evalJump, Body.exec, Term.exec, Val.eval, initial]

private theorem clearPlug :
    plugRTLWithStore model clearRegister initial (readRegister model.val) = Part.some (1, 0) := by
  rw [plugRTLWithStore, clearRun]
  simp [readRegister, Body.evalJump, Body.exec, Term.exec, Val.eval, upd, model]

/-- Plugging a raw final-store observer can distinguish two equal classes,
and in particular fails to preserve their refinement. -/
theorem finalStorePlug_not_monotone :
    ∃ (lhs rhs : CFG Unit Nat Unit) (m : PairModel Unit Part Nat) (store : Unit → Nat)
      (next : Transfer Unit Nat Nat → Part (Nat × Nat)),
      (Quotient.mk _ lhs : RTLClass Unit Nat Unit Part Nat) = Quotient.mk _ rhs ∧
      ¬ plugRTLWithStore m lhs store next ≤ plugRTLWithStore m rhs store next := by
  refine ⟨keepRegister, clearRegister, model, initial, readRegister model.val, sameClass, ?_⟩
  rw [keepPlug, clearPlug]
  intro included
  have returned := included (1, 1) (Part.mem_some _)
  simp at returned

-- The same reader may use a common external store, in which case the two
-- observations are equal.
example : plugRTL model (Quotient.mk _ keepRegister) initial (withExternalStore initial (readRegister model.val)) =
    plugRTL model (Quotient.mk _ clearRegister) initial (withExternalStore initial (readRegister model.val)) :=
  congrArg (fun program => plugRTL model program initial (withExternalStore initial (readRegister model.val)))
    sameClass

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement
