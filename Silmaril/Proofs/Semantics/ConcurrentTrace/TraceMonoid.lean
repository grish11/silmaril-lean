module

public import Silmaril.Semantics.ConcurrentTrace.TraceMonoid.Defs

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.TraceMonoid

open Silmaril.Semantics.ConcurrentTrace.TraceMonoid

universe u v

variable {A : Type u} {B : Type v} {I : A → A → Prop} {J : B → B → Prop}

theorem map_ofWord (f : A → B) (h : ∀ ⦃a b⦄, I a b → J (f a) (f b)) (word : List A) :
    map f h (ofWord I word) = ofWord J (word.map f) := by
  induction word with
  | nil => simp
  | cons a word ih => simp [ih]

theorem singleton_mul_comm_iff (hsymm : Std.Symm I) (a b : A) :
    singleton I a * singleton I b = singleton I b * singleton I a ↔ a = b ∨ I a b := by
  classical
  refine ⟨fun heq => ?_, fun h => h.elim (fun h => h ▸ rfl) swap⟩
  by_contra h
  have hne : a ≠ b := fun hab => h (.inl hab)
  have hdep : ¬ I a b := fun hab => h (.inr hab)
  -- On a dependent pair, retaining just these two labels is a free-monoid observation.
  let retain (x : A) : FreeMonoid A := if x = a ∨ x = b then FreeMonoid.of x else 1
  have hcomm : ∀ ⦃x y⦄, I x y → retain x * retain y = retain y * retain x := by
    intro x y hxy
    by_cases hx : x = a ∨ x = b <;> by_cases hy : y = a ∨ y = b <;> simp [retain, hx, hy]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact (hdep hxy).elim
    · exact (hdep (hsymm.symm _ _ hxy)).elim
    · rfl
  have hobs := congrArg (fun x => (lift retain hcomm x).toList) heq
  have hlists : [a, b] = [b, a] := by
    simpa [map_mul, retain, FreeMonoid.toList_mul] using hobs
  exact hne (List.cons.inj hlists).1

end Silmaril.Proofs.Semantics.ConcurrentTrace.TraceMonoid
