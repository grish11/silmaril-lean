module

public import Silmaril.Semantics.NondeterministicTrace.Defs
import Silmaril.Proofs.Semantics.NondeterministicTrace.Finite

public section

namespace Silmaril.Semantics.NondeterministicTrace.Finite

open Silmaril.Elgot

universe u

variable {W A B : Type u}

@[simp] theorem outcomes_ofOutcomes (s : Set (A × W)) :
    outcomes (ofOutcomes s) = s := rfl

theorem outcomes_injective : Function.Injective (outcomes : Finite W A → Set (A × W)) :=
  Proofs.Semantics.NondeterministicTrace.Finite.outcomes_injective

variable [Monoid W]

@[simp] theorem outcomes_pure (a : A) :
    outcomes (pure a : Finite W A) = {(a, 1)} := rfl

theorem mem_bind {p : Finite W A} {k : A → Finite W B} {b : B} {w : W} :
    (b, w) ∈ outcomes (p >>= k) ↔
      ∃ a u v, (a, u) ∈ p.outcomes ∧ (b, v) ∈ (k a).outcomes ∧ u * v = w :=
  Proofs.Semantics.NondeterministicTrace.Finite.mem_bind

theorem outcomes_bind_pure (p : Finite W A) (f : A → B) :
    outcomes (p >>= pure ∘ f) = Prod.map f id '' p.outcomes :=
  Proofs.Semantics.NondeterministicTrace.Finite.outcomes_bind_pure p f

/-- A returned observation arises by a finite run with the accumulated log. -/
theorem mem_iter (f : A → Finite W (B ⊕ A)) (a : A) (b : B) (w : W) :
    (b, w) ∈ outcomes (iter f a) ↔ Runs f a b w :=
  Proofs.Semantics.NondeterministicTrace.Finite.mem_iter f a b w

theorem unfold_eq_bind (f : A → Finite W (B ⊕ A)) (k : A → Set (B × W)) (a : A) :
    unfoldLoop f k a = outcomes (f a >>= Sum.elim pure (fun next => ofOutcomes (k next))) :=
  Proofs.Semantics.NondeterministicTrace.Finite.unfold_eq_bind f k a

/-- Transformer iteration is the least fixed point of the trace unfolding. -/
theorem iter_eq_lfp (f : A → Finite W (B ⊕ A)) :
    (fun a => outcomes (iter f a)) = (unfoldLoop f).lfp :=
  Proofs.Semantics.NondeterministicTrace.Finite.iter_eq_lfp f

end Silmaril.Semantics.NondeterministicTrace.Finite
