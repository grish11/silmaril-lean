module

import Silmaril.Logic.Abstraction.Propositional.Thms

namespace Silmaril.Logic.Abstraction.ComparisonRegression

open CategoryTheory Silmaril.Logic.Institution.Examples

private def emptyStructure (D : Type) (h : Nonempty D) :
    UFOL.Structure (Propositional.signature PEmpty) where
  carrier := D
  nonempty := h
  op o := o.elim
  rel r := r.2.elim

-- Every object has a different object. The equality reads both binder depths.
private def hasOther : UFOL.Sentence (Propositional.signature PEmpty) :=
  .all (.not (.all (.eq (.var 0) (.var 1))))

example : ¬ (FirstOrder.model (emptyStructure Unit ⟨()⟩)).Sat (FirstOrder.sentence hasOther) := by
  intro h
  have holds := (FirstOrder.sat_sentence _ _).mp h
  change ∀ x : Unit, ¬ ∀ y : Unit, y = x at holds
  exact holds () (fun y => Subsingleton.elim y ())

example : (FirstOrder.model (emptyStructure Bool ⟨false⟩)).Sat (FirstOrder.sentence hasOther) := by
  apply (FirstOrder.sat_sentence _ _).mpr
  change ∀ x : Bool, ¬ ∀ y : Bool, y = x
  intro x h
  cases x
  · exact Bool.noConfusion (h true)
  · exact Bool.noConfusion (h false)

-- The full institution admits an algebra with the same carrier and truth classification
-- whose operators, including the symbol translating first-order truth, always return false.
private noncomputable def uninterpreted :
    Model (FirstOrder.signature (Propositional.signature PEmpty)) :=
  let A : Algebra (FirstOrder.signature (Propositional.signature PEmpty)) :=
    ⟨Unit ⊕ Bool, ⟨.inl ()⟩, fun _ _ => .inr false⟩
  ⟨A, (FirstOrder.model (emptyStructure Unit ⟨()⟩)).truth, ValuationSpace.full A⟩

example : ¬ uninterpreted.Sat (FirstOrder.sentence .tt) := by
  intro h
  let ν : Valuation (Unit ⊕ Bool) := fun _ _ _ => .inl ()
  have bad := h ν (Set.mem_univ _) True (by simp [FirstOrder.sentence, Rule.formula]) trivial
  change Sum.inr false = (Sum.inr true : Unit ⊕ Bool) at bad
  cases bad

private def collapse : Bool ⟶ Unit := TypeCat.ofHom fun _ => ()
private def φ : PL.Formula Bool := .imp (.var true) (.or (.var false) .bot)

-- Collapsing the variables changes the observation. Reduct along that nonidentity
-- map agrees with evaluating the renamed formula on its singleton canonical model.
example (v : Unit → Prop) :
    ((Propositional.model v).reduct
      (FirstOrder.signatureFunctor.map (Propositional.signatureFunctor.map collapse))).Sat
        (Propositional.sentence φ) := by
  rw [Propositional.model_reduct]
  exact (Propositional.sat_sentence _ _).mpr (fun h => Or.inl h)

end Silmaril.Logic.Abstraction.ComparisonRegression
