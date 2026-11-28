module

public import Silmaril.Semantics.Brookes.Iteration.Defs
public import Silmaril.Semantics.Brookes.Parallel.Thms
import Silmaril.Proofs.Semantics.Brookes.Iteration

public section

namespace Silmaril.Semantics.Brookes.Behavior

universe u v w

open Silmaril.Semantics.Domain OmegaCompletePartialOrder
open Silmaril.Elgot

variable {Store : Type u} {X : Type v} {Y : Type w}

/-- Bind is monotone in the input and the continuation. -/
theorem bind_mono {p q : Behavior Store X} {k l : X → Behavior Store Y}
    (hp : p ≤ q) (hk : k ≤ l) : p.bind k ≤ q.bind l :=
  Proofs.Semantics.Brookes.Iteration.bind_mono hp hk

/-- Bind preserves unions in the first operand. -/
theorem bind_union_left {ι : Type*} (p : ι → Behavior Store X) (k : X → Behavior Store Y) :
    (union p).bind k = union (fun i => (p i).bind k) :=
  Proofs.Semantics.Brookes.Iteration.bind_union_left p k

/-- Bind preserves pointwise unions of continuations. -/
theorem bind_union_right {ι : Type*} (p : Behavior Store X) (k : ι → X → Behavior Store Y) :
    p.bind (fun x => union (fun i => k i x)) =
      union (fun i => p.bind (k i)) :=
  Proofs.Semantics.Brookes.Iteration.bind_union_right p k

/-- Bottom cannot supply a result to the continuation. -/
theorem bot_bind (k : X → Behavior Store Y) : (⊥ : Behavior Store X).bind k = ⊥ :=
  Proofs.Semantics.Brookes.Iteration.bot_bind k

/-- A continuation that is always bottom supplies no completed trace. -/
theorem bind_bot (p : Behavior Store X) : p.bind (fun _ => (⊥ : Behavior Store Y)) = ⊥ :=
  Proofs.Semantics.Brookes.Iteration.bind_bot p

/-- Loop unfolding is ω-Scott continuous. -/
theorem unfold_continuous (body : X → Behavior Store (Y ⊕ X)) :
    ωScottContinuous (unfoldLoop body) :=
  Proofs.Semantics.Brookes.Iteration.unfold_continuous body

/-- Finite approximants increase with the bound. -/
theorem approx_monotone (body : X → Behavior Store (Y ⊕ X)) :
    Monotone (approx body) :=
  Proofs.Semantics.Brookes.Iteration.approx_monotone body

/-- Every completed observation is already present at a finite bound. -/
theorem iterate_accepts_iff {body : X → Behavior Store (Y ⊕ X)} {x : X}
    {trace : Trace Store} {y : Y} :
    (iterate body x).accepts trace y ↔ ∃ n, (approx body n x).accepts trace y :=
  Iff.rfl

/-- The omega union computes the repository’s Kleene fixed point. -/
theorem iterate_eq_fix (body : X → Behavior Store (Y ⊕ X)) :
    iterate body = fix (ContinuousHom.ofFun _ (unfold_continuous body)) :=
  Proofs.Semantics.Brookes.Iteration.iterate_eq_fix body

/-- Iteration is a fixed point of one unfolding. -/
theorem iterate_unfold (body : X → Behavior Store (Y ⊕ X)) :
    unfoldLoop body (iterate body) = iterate body :=
  Proofs.Semantics.Brookes.Iteration.iterate_unfold body

/-- Iteration lies below every pre-fixed point of unfolding. -/
theorem iterate_least (body : X → Behavior Store (Y ⊕ X)) (k : X → Behavior Store Y)
    (h : unfoldLoop body k ≤ k) : iterate body ≤ k :=
  Proofs.Semantics.Brookes.Iteration.iterate_least body k h

section Elgot

variable {A B C : Type v}

/-- Postcomposition acts only on returned values. -/
theorem iterate_naturality (f : A → Behavior Store (B ⊕ A)) (g : B → Behavior Store C) :
    (fun x => (iterate f x).bind g) = iterate (mapReturn f g) :=
  Proofs.Semantics.Brookes.Iteration.iterate_naturality f g

/-- Two successive feedback summands can be merged. -/
theorem iterate_codiagonal (f : A → Behavior Store ((B ⊕ A) ⊕ A)) :
    iterate (iterate f) = iterate (flattenBody f) :=
  Proofs.Semantics.Brookes.Iteration.iterate_codiagonal f

/-- A pure simulation of loop states commutes with iteration. -/
theorem iterate_uniformity (f : A → Behavior Store (B ⊕ A))
    (g : C → Behavior Store (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iterate f = iterate g ∘ h :=
  Proofs.Semantics.Brookes.Iteration.iterate_uniformity f g h comm

end Elgot

/-- An unchanged pure context can be carried through every iteration. -/
theorem iterate_strength {D : Type*} (f : X → Behavior Store (Y ⊕ X)) (d : D) (x : X) :
    (iterate f x).strength d = iterate (strengthBody f) (d, x) :=
  Proofs.Semantics.Brookes.Iteration.iterate_strength f d x

/-- The same context law holds when strength is written as parallel with a pure operand. -/
theorem iterate_parallel_ret {D : Type*} (f : X → Behavior Store (Y ⊕ X)) (d : D) (x : X) :
    (ret d).parallel (iterate f x) = iterate (strengthBody f) (d, x) := by
  rw [parallel_ret_left]
  exact iterate_strength f d x

/-- A body that can only continue has empty completed behavior. -/
theorem iterate_inr_eq_bot (f : X → Behavior Store (Y ⊕ X))
    (h : ∀ x trace y, ¬(f x).accepts trace (.inl y)) : iterate f = ⊥ :=
  Proofs.Semantics.Brookes.Iteration.iterate_inr_eq_bot f h

/-- At any initial store a pure return has an observation that bottom lacks. -/
theorem ret_ne_bot (s : Store) (y : Y) : ret y ≠ (⊥ : Behavior Store Y) :=
  Proofs.Semantics.Brookes.Iteration.ret_ne_bot s y

/-- The finite shared-store behavior monad has complete Elgot iteration. -/
instance : LawfulElgotMonad (Behavior Store) where
  fixpoint f := (iterate_unfold f).symm
  naturality := iterate_naturality
  codiagonal := iterate_codiagonal
  uniformity f g h comm := (iterate_uniformity f g h comm).trans
    (funext fun x => (ret_bind (h x) (iterate g)).symm)

end Silmaril.Semantics.Brookes.Behavior
