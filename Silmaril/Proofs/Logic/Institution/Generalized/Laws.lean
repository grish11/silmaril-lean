module

public import Silmaril.Logic.Institution.Generalized.Defs

public section

namespace Silmaril.Proofs.Logic.Institution.Generalized

open CategoryTheory Opposite
open Silmaril.Logic.Institution.Generalized

universe u v w m₁ m₂ d

variable {Sign : Type u} [Category.{v} Sign] {D : Type d}

theorem le_eval_map_comp [Preorder D] (I : LaxInstitution.{u,v,w,m₁,m₂,d} Sign D)
    {S T U : Sign} (σ : S ⟶ T) (τ : T ⟶ U) (M : I.Mod.obj (op U)) (φ : I.Sen.obj S) :
    I.eval S ((I.Mod.map (σ ≫ τ).op).toFunctor.obj M) φ ≤
      I.eval U M (I.Sen.map (σ ≫ τ) φ) := by
  rw [op_comp, Functor.map_comp, I.Sen.map_comp_apply]
  exact (I.le_eval_map σ ((I.Mod.map τ.op).toFunctor.obj M) φ).trans
    (I.le_eval_map τ M (I.Sen.map σ φ))

theorem ofCompletions_image {M N : Type*} (reduct : N → M) (completions : Set N)
    (holds : M → Prop) (holds' : N → Prop)
    (commutes : ∀ n ∈ completions, holds' n ↔ holds (reduct n)) :
    Evidence.ofCompletions completions holds' =
      Evidence.ofCompletions (reduct '' completions) holds := by
  apply Evidence.ext
  · apply propext
    constructor
    · rintro h _ ⟨n, hn, rfl⟩
      exact (commutes n hn).mp (h n hn)
    · intro h n hn
      exact (commutes n hn).mpr (h _ ⟨n, hn, rfl⟩)
  · apply propext
    constructor
    · rintro h _ ⟨n, hn, rfl⟩ hp
      exact h n hn ((commutes n hn).mpr hp)
    · intro h n hn hp
      exact h _ ⟨n, hn, rfl⟩ ((commutes n hn).mp hp)

theorem ofThree_injective : Function.Injective Evidence.ofThree := by
  intro x y h
  have pos := congrArg Evidence.positive h
  have neg := congrArg Evidence.negative h
  cases x with
  | none => cases y with
    | none => rfl
    | some y => cases y <;> simp [Evidence.ofThree] at pos neg
  | some x =>
    cases y with
    | none => cases x <;> simp [Evidence.ofThree] at pos neg
    | some y => cases x <;> cases y <;> simp_all [Evidence.ofThree]

end Silmaril.Proofs.Logic.Institution.Generalized
