module

public import Silmaril.Logic.Matching.GeneralFixedPoint.Variables.Thms
public import Silmaril.Logic.Matching.FirstOrder.Algebraic

@[expose] public section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S}

/-- Ordinary algebraic terms are actual singleton element replacements. The
singleton premise of simultaneous substitution is discharged by evaluation. -/
theorem Pattern.denote_substitute_terms (M : Algebraic.ManySorted.Model A)
    (inhabited : ∀ s, Nonempty (M.carrier s)) {r k a b : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {Q : Fin a → S} {Δ : Fin b → S} {s : S}
    (p : Pattern A P Γ s) (σ : ∀ i, Pattern A Q Δ (P i))
    (terms : ∀ i, Algebraic.ManySorted.Term A Δ (Γ i))
    (v : ∀ i, M.carrier (Δ i)) (η : ∀ i, Set (M.carrier (Q i))) :
    (p.substitute σ (fun i => .base (FirstOrder.Pattern.ofTerm (terms i)))).denote
        (FirstOrder.Model.ofAlgebra M inhabited) v η =
      p.denote (FirstOrder.Model.ofAlgebra M inhabited)
        (fun i => M.eval v (terms i))
        (fun i => (σ i).denote (FirstOrder.Model.ofAlgebra M inhabited) v η) :=
  p.denote_substitute (FirstOrder.Model.ofAlgebra M inhabited) σ
    (fun i => .base (FirstOrder.Pattern.ofTerm (terms i))) v η
    (fun i => M.eval v (terms i))
    (fun i => FirstOrder.Model.denote_ofTerm M inhabited v (terms i))

end Silmaril.Logic.Matching.GeneralFixedPoint
