module

public import Silmaril.Logic.Matching.FirstOrder.Defs

@[expose] public section
namespace Silmaril.Logic.Matching.FirstOrder
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S}

/-- Nonempty ordinary algebras are matching models with singleton interpretations.
The carrier hypothesis is necessary because the algebraic API also allows empty sorts. -/
def Model.ofAlgebra (M : Algebraic.ManySorted.Model A)
    (inhabited : ∀ s, Nonempty (M.carrier s)) : Model A :=
  ⟨M.carrier, inhabited, fun op args => {M.operation op args}⟩

def Pattern.ofTerm {k : Nat} {Γ : Fin k → S} {s : S} : Algebraic.ManySorted.Term (k := k) A Γ s → Pattern A Γ s
  | .var i => .var i
  | .app op args => .app op (fun i => ofTerm (args i))

/-- The source's ordinary-algebra special case is proved, not assumed. -/
theorem Model.denote_ofTerm (M : Algebraic.ManySorted.Model A)
    (inhabited : ∀ s, Nonempty (M.carrier s)) {k : Nat} {Γ : Fin k → S} {s : S}
    (v : (i : Fin k) → M.carrier (Γ i)) (t : Algebraic.ManySorted.Term A Γ s) :
    (ofAlgebra M inhabited).denote v (Pattern.ofTerm t) = {M.eval (Γ := Γ) v t} := by
  induction t with
  | var => rfl
  | app op args ih =>
    ext result
    change (∃ values, (∀ i, values i ∈ (ofAlgebra M inhabited).denote v
      (Pattern.ofTerm (args i))) ∧ result = M.operation op values) ↔
      result = M.operation op (fun i => M.eval v (args i))
    constructor
    · rintro ⟨values, members, result_eq⟩
      have same : values = (fun i => M.eval v (args i)) := by
        funext i
        have member := members i
        rw [ih i] at member
        exact member
      simpa only [same] using result_eq
    · intro result_eq
      refine ⟨(fun i => M.eval v (args i)), ?_, result_eq⟩
      intro i
      rw [ih i]
      rfl
end Silmaril.Logic.Matching.FirstOrder
