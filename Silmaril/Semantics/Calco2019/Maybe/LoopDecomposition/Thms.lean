module

public import Silmaril.Semantics.Calco2019.Maybe.LoopDecomposition.Defs
public import Silmaril.Semantics.Calco2019.Parametrized
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Silmaril.Proofs.Semantics.Calco2019.Maybe.LoopDecomposition

/-! # Elgot comparison for decomposable deterministic loops -/

public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

/-- The full category of guarded Elgot monads whose guard is total. -/
abbrev TotalElgot (P : Coproducts C) :=
  ObjectProperty.FullSubcategory (GuardedElgotMonad.IsElgot (P := P))

variable [HasInitial C] {E X Y : C} (terminal : IsTerminal E)
  (S T : GuardedElgotMonad P) (hs : S.IsElgot) (ht : T.IsElgot) (hm : S.monad = monad P E)

include terminal in
/-- The comparison preserves the solution of a pure loop with a finite-exit and recurrence
decomposition. The finite branches compute by unfolding, and the residual branch by uniformity. -/
theorem comparison_iteratePure {f : X ⟶ P.sum Y X} (D : LoopDecomposition f) :
    iteratePure S hs f ≫ eqToHom (congrArg (fun M : CategoryTheory.Monad C => M.obj Y) hm) ≫
      (comparison T ht E).app Y = iteratePure T ht f :=
  Proofs.comparison_iteratePure T ht terminal S hs hm D

include terminal in
/-- If all pure loops admit the decomposition, Maybe's comparison preserves arbitrary
iteration. Its proof treats explicit failure as a distinguished pure exit and uses naturality. -/
theorem comparison_iterates
    (decompose : ∀ {A B : C} (f : A ⟶ P.sum B A), Nonempty (LoopDecomposition f))
    (f : X ⟶ S.monad.obj (P.sum Y X)) :
    let m (Y : C) := eqToHom (congrArg (fun M : CategoryTheory.Monad C => M.obj Y) hm) ≫
      (comparison T ht E).app Y
    (S.iteration.iterate (kleisliArrow f) (hs (kleisliArrow f))).of ≫ m Y =
      (T.iteration.iterate (kleisliArrow (f ≫ m (P.sum Y X)))
        (ht (kleisliArrow (f ≫ m (P.sum Y X))))).of :=
  Proofs.comparison_iterates T ht terminal S hs hm decompose f

/-- Any total Elgot structure on Maybe is initial among total Elgot monads if
each pure body has the finite-exit and recurrence decomposition. -/
noncomputable def initialOfDecomposition
    (decompose : ∀ {A B : C} (f : A ⟶ P.sum B A), Nonempty (LoopDecomposition f)) :
    IsInitial (⟨S, hs⟩ : TotalElgot P) :=
  IsInitial.ofUniqueHom
    (fun T => ObjectProperty.homMk {
      hom := hm.symm ▸ comparison T.obj T.property E
      guarded := fun _ _ => T.property _
      iteration := fun f _ => by
        have e := comparison_iterates terminal S T.obj hs T.property hm decompose f
        obtain ⟨M, _, _, _⟩ := S
        change M = monad P E at hm
        subst M
        simpa only [eqToHom_refl, Category.id_comp] using e })
    (fun T g => by
      apply ObjectProperty.hom_ext
      apply GuardedElgotMonadHom.ext
      apply MonadHom.ext
      funext X
      have e := comparison_unique T.obj T.property terminal S hs hm g.hom X
      obtain ⟨M, _, _, _⟩ := S
      change M = monad P E at hm
      subst M
      change g.hom.hom.app X = (comparison T.obj T.property E).app X
      simpa only [eqToHom_refl, Category.id_comp] using e)

end Silmaril.Calco2019.Maybe
