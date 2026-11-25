module

public import Silmaril.Semantics.Calco2019.CompletelyIterative.Defs
public import Silmaril.Semantics.Calco2019.Thms
import Silmaril.Proofs.Semantics.Calco2019.CompletelyIterative

/-! # The weak guard of a completely iterative monad -/

public section

universe u v

namespace Silmaril.Calco2019.IdealizedMonad

open CategoryTheory

variable {C : Type u} [Category.{v} C] {T : CategoryTheory.Monad C} (I : IdealizedMonad T)
  (P : Coproducts C)

/-- Weak guardedness satisfies Definition 6 for any idealized monad. -/
@[expose]
noncomputable def weakGuard : MonadGuardedness P T where
  guarded f := I.WeaklyGuarded P f
  trivial f := by exact Proofs.CompletelyIterative.trivial I P f
  parallel hf hg := by exact Proofs.CompletelyIterative.parallel I P hf hg
  compose h hf hg := by exact Proofs.CompletelyIterative.compose I P h hf hg

/-- A base-category factor also gives a Kleisli factor. -/
theorem stronglyGuarded_implies_weaklyGuarded {X Y Z : Kleisli T}
    {f : X ⟶ (P.kleisli T).sum Y Z}
    (hf : I.StronglyGuarded P (Y := Y) (Z := Z) f) :
    I.WeaklyGuarded P (Y := Y) (Z := Z) f :=
  ⟨(Kleisli.Adjunction.toKleisli T).map hf.choose, hf.choose_spec⟩

/-- Figure 1, right lower edge. Unique strong solutions imply unique weak solutions. -/
theorem weakGuard_iterative (h : I.CompletelyIterative P) :
    IsGuardedIterative P (I.weakGuard P) :=
  fun f hf => Proofs.CompletelyIterative.iterative I P h f hf

end Silmaril.Calco2019.IdealizedMonad
