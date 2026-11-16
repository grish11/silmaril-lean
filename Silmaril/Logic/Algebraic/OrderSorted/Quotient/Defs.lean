module

public import Silmaril.Logic.Algebraic.OrderSorted.Initial.Thms
public import Silmaril.Logic.Algebraic.Initial.Quotient.Thms

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Presented
open CategoryTheory Silmaril.Logic.Institution.Examples
variable (T : Initial.Theory) {k : Nat} (Γ : Fin k → T.sig.base.S)

/-- Congruence on actual principal-core terms, saturated under reflection along
injective coercions. Axiom instances require all declared context variables. -/
inductive Rel : {s : T.sig.base.S} → Free.Normal T.sig Γ s → Free.Normal T.sig Γ s → Prop where
  | refl {s} (a : Free.Normal T.sig Γ s) : Rel a a
  | symm {s} {a b : Free.Normal T.sig Γ s} : Rel a b → Rel b a
  | trans {s} {a b c : Free.Normal T.sig Γ s} : Rel a b → Rel b c → Rel a c
  | op {n w s} (o : (compiled T.sig).Op n w s)
      (a b : ∀ i, Free.Normal T.sig Γ (w i)) (h : ∀ i, Rel (a i) (b i)) :
      Rel ((Free.model T.sig Γ).algebra.op o a) ((Free.model T.sig Γ).algebra.op o b)
  | equation (e : Sentence T.sig) (he : ULift.up e ∈ T.axioms)
      (v : ∀ i, Free.Normal T.sig Γ (e.ctx i)) :
      Rel (e.lhs.eval (Free.model T.sig Γ).algebra v)
        (e.rhs.eval (Free.model T.sig Γ).algebra v)
  | reflect {s t} (h : s ≤ t) {a b : Free.Normal T.sig Γ s} :
      Rel (Free.coerce h a) (Free.coerce h b) → Rel a b

def setoid (s : T.sig.base.S) : Setoid (Free.Normal T.sig Γ s) :=
  ⟨Rel T Γ, ⟨Rel.refl, Rel.symm, Rel.trans⟩⟩

def algebra : Algebra T.sig where
  carrier s := Quotient (setoid T Γ s)
  op o args := Quotient.finLiftOn args
    (fun a => Quotient.mk _ ((Free.model T.sig Γ).algebra.op o a))
    (fun a b h => Quotient.sound (Rel.op o a b h))

theorem op_mk {n : Nat} {w : Fin n → T.sig.base.S} {s : T.sig.base.S}
    (o : (compiled T.sig).Op n w s) (args : ∀ i, Free.Normal T.sig Γ (w i)) :
    (algebra T Γ).op o (fun i => Quotient.mk _ (args i)) =
      Quotient.mk (setoid T Γ s) ((Free.model T.sig Γ).algebra.op o args) := by
  change Quotient.finLiftOn (S := fun i => setoid T Γ (w i))
    (fun i => Quotient.mk _ (args i)) _ _ = _
  exact congrFun (congrFun (Quotient.finLiftOn_mk args)
    (fun a => Quotient.mk (setoid T Γ s) ((Free.model T.sig Γ).algebra.op o a)))
    (fun a b h => Quotient.sound (Rel.op o a b h))

theorem coerce_mk {s t : T.sig.base.S} (h : s ≤ t) (a : Free.Normal T.sig Γ s) :
    (algebra T Γ).coerce h (Quotient.mk _ a) =
      Quotient.mk (setoid T Γ t) (Free.coerce h a) :=
  op_mk T Γ (.inclusion s t h) (fun _ => a)

/-- Quotients retain exactly the inhabited sorts of the existing free model. -/
theorem nonempty_carrier_iff (s : T.sig.base.S) :
    Nonempty ((algebra T Γ).carrier s) ↔ Nonempty (Free.Normal T.sig Γ s) :=
  nonempty_quotient_iff _

end Silmaril.Logic.Algebraic.OrderSorted.Presented
