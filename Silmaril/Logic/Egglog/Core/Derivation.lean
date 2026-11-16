module

public import Silmaril.Logic.Egglog.Core.Defs
public import Silmaril.Logic.Egg.Core.Explanation

@[expose] public section

namespace Silmaril.Logic.Egglog.Core

open Silmaril.Logic.Institution.Examples


namespace Atom
variable {S : Signature} {n m : Nat} {Γ : Fin n → S.S} {Δ : Fin m → S.S}

def instantiate (δ : ∀ i, EQ.Term S.toSignature Δ (Γ i)) : Atom S Γ → Atom S Δ
  | .equal e => .equal ⟨e.sort,Silmaril.Logic.Egg.Core.Pattern.instantiate δ e.lhs,Silmaril.Logic.Egg.Core.Pattern.instantiate δ e.rhs⟩
  | .relation r args => .relation r (fun i => Silmaril.Logic.Egg.Core.Pattern.instantiate δ (args i))
  | .row f args value => .row f (fun i => Silmaril.Logic.Egg.Core.Pattern.instantiate δ (args i)) (Silmaril.Logic.Egg.Core.Pattern.instantiate δ value)

theorem instantiate_holds (δ : ∀ i, EQ.Term S.toSignature Δ (Γ i)) (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (a : Atom S Γ) :
    (a.instantiate δ).Holds M ρ ↔ a.Holds M (fun i => (δ i).eval M.toAlgebra ρ) := by
  cases a <;> simp only [instantiate, Holds, Silmaril.Logic.Egg.Core.Equality.Holds,
    Silmaril.Logic.Egg.Core.Pattern.eval_instantiate]
end Atom

/-- Normalized ground rule firing records every matched premise. FD collisions in the
equality-table fragment justify equality of the two output terms. -/
inductive Derivation {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    (rules : Set (Rule S)) (facts : Set (Atom S Δ)) : Atom S Δ → Prop where
  | input {a} : a ∈ facts → Derivation rules facts a
  | fire (r : Rule S) (hr : r ∈ rules) (δ : ∀ i, EQ.Term S.toSignature Δ (r.context i))
      (premises : ∀ a ∈ r.body, Derivation rules facts (a.instantiate δ)) :
      Derivation rules facts (r.head.instantiate δ)
  | collision {n w s} (f : S.Function n w s) (args : ∀ i, EQ.Term S.toSignature Δ (w i))
      (x y : EQ.Term S.toSignature Δ s) :
      Derivation rules facts (.row f args x) → Derivation rules facts (.row f args y) →
      Derivation rules facts (.equal ⟨s,x,y⟩)

def StateHolds {S : Signature} {m : Nat} {Δ : Fin m → S.S} (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) (facts : Set (Atom S Δ)) : Prop := ∀ a ∈ facts, a.Holds M ρ

structure InsertStep {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    (rules : Set (Rule S)) (before after : Set (Atom S Δ)) where
  fact : Atom S Δ
  certificate : Derivation rules before fact
  result : after = insert fact before

end Silmaril.Logic.Egglog.Core
