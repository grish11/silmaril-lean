module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Parallel.Defs
public import Silmaril.Semantics.Categories.Freyd.Parallel.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Compatibility of ordered Freyd parallel with the native LetIter clauses -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open LocallyNameless (Derivation)
open ProofRelevant.Semantics.Categorical (contextualLoop duplicate extend retainLeft)
open scoped MonoidalCategory

universe u₁ u₂ u v w v₁ v₂

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [∀ X Y : C, Preorder (X ⟶ Y)] {J : V ⥤ C}

section Freyd

variable [FreydCategory J] (P : FreydCategory.OrderedParallel J)

/-- Tensoring with identity on the left agrees with native context retention. -/
theorem tensor_id_left_eq_retainLeft {R A B : V} (f : J.obj A ⟶ J.obj B) :
    P.tensor (𝟙 (J.obj R)) f = retainLeft J (R := R) f := by
  simpa only [retainLeft, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp] using P.whiskerLeft R f

/-- Sharing the context with an identity branch gives native context extension. -/
theorem par_id_left_eq_extend {R A : V} (f : J.obj R ⟶ J.obj A) :
    P.par (𝟙 (J.obj R)) f = extend J f := by
  simp only [FreydCategory.OrderedParallel.par, tensor_id_left_eq_retainLeft P,
    retainLeft, extend, duplicate]

end Freyd

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : Ctx ν τ} {n : Nat} {β : Isotope.BoundCtx τ n} {A B : τ}

/-- Reindexing the ambient values of a typed pair reindexes each branch. -/
theorem denotePar_reindex {R : V} (k : R ⟶ envObj M Γ β)
    {s t : LocallyNameless.Tm ν Φ n} (ds : Derivation Φ Γ β s A) (dt : Derivation Φ Γ β t B) :
    J.map k ≫ denotePar J P M ds dt =
      P.par (J.map k ≫ denote J M ds) (J.map k ≫ denote J M dt) ≫
        J.map (M.productIso A B).inv := by
  rw [denotePar, ← Category.assoc, P.par_reindex]

/-- The native sequential pair and parallel agree when both branch denotations are pure. -/
theorem denotePar_eq_pair_of_maps {s t : LocallyNameless.Tm ν Φ n}
    (ds : Derivation Φ Γ β s A) (dt : Derivation Φ Γ β t B)
    {f : envObj M Γ β ⟶ M.obj A} {g : envObj M Γ β ⟶ M.obj B}
    (hs : denote J M ds = J.map f) (ht : denote J M dt = J.map g) :
    denotePar J P M ds dt = denote J M (.pair ds dt) := by
  simp only [denotePar, denote, hs, ht, P.par_maps, pair_maps_eq_map_lift]

/-- Rewriting the context extension in a native let leaves its denotation equal. -/
theorem denote_let₁_with_par {s : LocallyNameless.Tm ν Φ n} {t : LocallyNameless.Tm ν Φ (n + 1)}
    (ds : Derivation Φ Γ β s A) (dt : Derivation Φ Γ (.snoc β A) t B) :
    denote J M (.let₁ ds dt) =
      P.par (𝟙 (J.obj (envObj M Γ β))) (denote J M ds) ≫
        J.map (envSnocIso M Γ β A).hom ≫ denote J M dt := by
  simp only [denote, ProofRelevant.Semantics.Categorical.bind, par_id_left_eq_extend P]

/-- Rewriting the native seed extension leaves the chosen contextual loop in place. -/
theorem denote_iter_with_par {s : LocallyNameless.Tm ν Φ n} {t : LocallyNameless.Tm ν Φ (n + 1)}
    (ds : Derivation Φ Γ β s A) (dt : Derivation Φ Γ (.snoc β A) t (coprod B A)) :
    denote J M (.iter ds dt) =
      P.par (𝟙 (J.obj (envObj M Γ β))) (denote J M ds) ≫
        contextualLoop J (J.map (envSnocIso M Γ β A).hom ≫
          denote J M dt ≫ J.map (M.coprodIso B A).hom) := by
  simp only [denote, ProofRelevant.Semantics.Categorical.bind, par_id_left_eq_extend P]

end Silmaril.Isotope.LetIter.Semantics.Categorical
