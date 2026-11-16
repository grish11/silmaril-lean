module

public import Silmaril.Logic.Egg.Core.Defs

@[expose] public section

namespace Silmaril.Logic.Egg.Core

open Silmaril.Logic.Institution.Examples

namespace Pattern
variable {S : Signature} {n m : Nat} {Γ : Fin n → S.S} {Δ : Fin m → S.S}

/-- An engine match substitution is a correctly sorted term for every pattern variable. -/
def instantiate (δ : ∀ i, EQ.Term S Δ (Γ i)) : {s : S.S} → EQ.Term S Γ s → EQ.Term S Δ s
  | _, .var i => δ i
  | _, .app o args => .app o (fun i => instantiate δ (args i))

theorem eval_instantiate (δ : ∀ i, EQ.Term S Δ (Γ i)) (M : Model S)
    (ρ : ∀ i, M.carrier (Δ i)) {s : S.S} (t : EQ.Term S Γ s) :
    (instantiate δ t).eval M ρ = t.eval M (fun i => (δ i).eval M ρ) := by
  induction t with
  | var i => rfl
  | app o args ih =>
    simp only [instantiate, EQ.Term.eval]
    congr 1
    funext i
    exact ih i
end Pattern

/-- Normalized explanation evidence. An untrusted rule name is insufficient: membership,
its actual substitution, and explanations for every guard are all required. -/
inductive Explanation {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    (rules : Set (Rule S)) (premises : Set (Equality S Δ)) :
    {s : S.S} → EQ.Term S Δ s → EQ.Term S Δ s → Prop where
  | premise {s} {a b : EQ.Term S Δ s} : ⟨s,a,b⟩ ∈ premises → Explanation rules premises a b
  | refl {s} (a : EQ.Term S Δ s) : Explanation rules premises a a
  | symm {s} {a b : EQ.Term S Δ s} : Explanation rules premises a b → Explanation rules premises b a
  | trans {s} {a b c : EQ.Term S Δ s} : Explanation rules premises a b →
      Explanation rules premises b c → Explanation rules premises a c
  | congr {n} {w : Fin n → S.S} {s} (o : S.Op n w s)
      (a b : ∀ i, EQ.Term S Δ (w i)) :
      (∀ i, Explanation rules premises (a i) (b i)) →
      Explanation rules premises (.app o a) (.app o b)
  | rewrite (r : Rule S) (hr : r ∈ rules) (δ : ∀ i, EQ.Term S Δ (r.context i))
      (guards : ∀ e ∈ r.guards, Explanation rules premises
        (Pattern.instantiate δ e.lhs) (Pattern.instantiate δ e.rhs)) :
      Explanation rules premises (Pattern.instantiate δ r.conclusion.lhs)
        (Pattern.instantiate δ r.conclusion.rhs)

/-- A finite union/saturation event adds exactly the explained equality to a state. -/
structure UnionStep {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    (rules : Set (Rule S)) (before after : Set (Equality S Δ)) where
  equality : Equality S Δ
  certificate : Explanation rules before equality.lhs equality.rhs
  result : after = insert equality before

/-- State invariants are algebraic equalities, not arbitrary union-find representative IDs. -/
def StateHolds {S : Signature} {m : Nat} {Δ : Fin m → S.S}
    (M : Model S) (ρ : ∀ i, M.carrier (Δ i)) (state : Set (Equality S Δ)) : Prop :=
  ∀ e ∈ state, e.Holds M ρ

end Silmaril.Logic.Egg.Core
