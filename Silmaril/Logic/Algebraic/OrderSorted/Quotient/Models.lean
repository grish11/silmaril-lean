module

public import Silmaril.Logic.Algebraic.OrderSorted.Quotient.Defs
public import Silmaril.Proofs.Logic.Algebraic.OrderSorted.Quotient.Coherence

@[expose] public section
namespace Silmaril.Logic.Algebraic.OrderSorted.Presented
open CategoryTheory

def coherentModel (T : Initial.Theory) {k : Nat} (Γ : Fin k → T.sig.base.S) : Model T.sig :=
  ⟨algebra T Γ, coherent T Γ⟩

/-- The projection preserves all actual base and coercion operations. -/
def projection (T : Initial.Theory) {k : Nat} (Γ : Fin k → T.sig.base.S) :
    Free.model T.sig Γ ⟶ coherentModel T Γ where
  map _ t := Quotient.mk _ t
  map_op o args := (op_mk T Γ o args).symm

end Silmaril.Logic.Algebraic.OrderSorted.Presented
