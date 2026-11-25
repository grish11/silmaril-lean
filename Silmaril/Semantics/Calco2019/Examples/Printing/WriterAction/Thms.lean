module

public import Silmaril.Semantics.Calco2019.Examples.Printing.WriterAction.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.WriterAction

/-! # The ordinary writer obstruction and the productive stream extension -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.WriterAction

variable {A M X : Type u}

instance [MulAction (FreeMonoid A) M] : LawfulMonad (WriterAction A M) := Proofs.lawful

/-- The nonempty-word guard from Example 10(4), for any choice of terminal action. -/
noncomputable def guard [MulAction (FreeMonoid A) M] : TypeKleisli.Guard (WriterAction A M) :=
  Proofs.guard

theorem guard_iff {Y Z : Type u} [MulAction (FreeMonoid A) M]
    (f : X → WriterAction A M (Y ⊕ Z)) : guard.holds f ↔ Guarded f := by
  unfold guard
  rfl

noncomputable def categorical [MulAction (FreeMonoid A) M] :
    MonadGuardedness typeCoproducts (CategoryTheory.ofTypeMonad (WriterAction A M)) :=
  TypeKleisli.categoricalGuard guard

theorem letterLoop_guarded (a : A) : Guarded (letterLoop (M := M) a) :=
  Proofs.letter_guarded a

/-- There is no terminal effect in the empty-action writer. -/
def ordinaryEquiv (A X : Type u) : WriterAction A PEmpty.{u + 1} X ≃ List A × X :=
  Proofs.ordinaryEquiv A X

attribute [local instance] emptyAction streamAction nonemptyWordAction singletonAction

/-- The ordinary writer has a guarded loop with no fixpoint. -/
theorem ordinary_not_iterative (a : A) :
    ¬ (categorical (A := A) (M := PEmpty.{u + 1})).Iterative :=
  fun h => Proofs.ordinary_no_unique a ((TypeKleisli.iterative_iff guard).1 h)

/-- An inhabited left action alone does not ensure guarded iteration. Prefixing
nonempty finite words always increases their length on a one-letter loop. -/
theorem inhabited_action_counterexample (a : A) :
    Nonempty {w : List A // w ≠ []} ∧
      ¬ (categorical (A := A) (M := {w : List A // w ≠ []})).Iterative :=
  ⟨⟨⟨[a], by simp⟩⟩, fun h => Proofs.words_no_unique a ((TypeKleisli.iterative_iff guard).1 h)⟩

/-- The extension by infinite streams has unique guarded solutions. -/
theorem stream_guarded_iterative (A : Type u) :
    (categorical (A := A) (M := ℕ → A)).Iterative :=
  (TypeKleisli.iterative_iff (guard (A := A) (M := ℕ → A))).2 (Proofs.streams_iterative A)

/-- The stream carrier is final for the coalgebra of emitting a letter and taking a step. -/
theorem streams_final (out : X → A × X) :
    ∃! f : X → ℕ → A, (∀ x, f x 0 = (out x).1) ∧
      ∀ x n, f x (n + 1) = f (out x).2 n :=
  Proofs.streams_final out

/-- A singleton receives a unique equivariant map from every left action. -/
theorem singleton_action_terminal [MulAction (FreeMonoid A) M] :
    ∃! f : M → PUnit.{u + 1}, ∀ (word : FreeMonoid A) x, f (word • x) = word • f x :=
  Proofs.singleton_action_terminal

/-- With a letter, the singleton is not initial among inhabited left actions. -/
theorem no_singleton_to_words (a : A) :
    ¬ ∃ f : PUnit.{u + 1} → {w : List A // w ≠ []},
      ∀ (word : FreeMonoid A) x, f (word • x) = word • f x :=
  Proofs.no_singleton_to_words a

/-- Stream finality as a coalgebra is distinct from terminality as a left action. -/
theorem no_singleton_to_streams (a b : A) (hab : a ≠ b) :
    ¬ ∃ f : PUnit.{u + 1} → ℕ → A, ∀ (word : FreeMonoid A) x, f (word • x) = word • f x :=
  Proofs.no_singleton_to_streams a b hab

end Silmaril.Calco2019.Examples.Printing.WriterAction
