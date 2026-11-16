module

public import Silmaril.Logic.Institution.Structured.Constraints.Structured
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Category.Cat.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

@[expose] public section
namespace Silmaril.Logic.Institution.Structured.Constraints
open CategoryTheory CategoryTheory.Limits Opposite Silmaril.Logic.Institution
universe u
noncomputable section
variable {Sign : Type u} [Category.{u} Sign] (I : Sign ⥤ Room.{u,u,u})

/-- Exactness makes the model category of an actual initial theory terminal.
This proves the categorical premise of the source's initial-model example. -/
def initialTheoryModels_isTerminal (hExact : SemanticModels.Exact I)
    (T : Spec I) (hT : IsInitial T) : IsTerminal (Cat.of (SemanticModels.Models I T)) := by
  letI : PreservesColimitsOfSize.{u,u} (SemanticModels.institution I ⋙ Room.modFunctor) := hExact
  have : PreservesColimitsOfSize.{0,0} (SemanticModels.institution I ⋙ Room.modFunctor) :=
    preservesColimitsOfSize_shrink _
  exact (hT.isInitialObj (SemanticModels.institution I ⋙ Room.modFunctor) T).unop _

/-- The terminal model category has a unique morphism between each pair of
models. This derives the premise of `freeAt_iff_initial` from exactness. -/
@[instance_reducible] def initialTheoryModelHomUnique (hExact : SemanticModels.Exact I)
    (T : Spec I) (hT : IsInitial T) (M N : SemanticModels.Models I T) : Unique (M ⟶ N) := by
  let e := Cat.equivOfIso (Cat.isoDiscretePUnitOfIsTerminal (initialTheoryModels_isTerminal I hExact T hT))
  let F : SemanticModels.Models I T ⥤ Discrete PUnit.{u+1} := e.functor
  let g : F.obj M ⟶ F.obj N := eqToHom (Subsingleton.elim _ _)
  refine ⟨⟨F.preimage g⟩, ?_⟩
  intro f
  apply F.map_injective
  exact Subsingleton.elim _ _

/-- Along a map out of an initial theory, the free-extension condition is
exactly initial-model semantics, derived from original exactness alone. -/
theorem freeAt_from_initialTheory_iff (hExact : SemanticModels.Exact I)
    (T₀ T : Spec I) (hT₀ : IsInitial T₀) (H : T₀ ⟶ T)
    (M : SemanticModels.Models I T) :
    FreeAt (SemanticModels.reduct I H) M ↔ Nonempty (IsInitial M) :=
  freeAt_iff_initial _ _ (fun N => initialTheoryModelHomUnique I hExact T₀ hT₀
    ((SemanticModels.reduct I H).obj M) ((SemanticModels.reduct I H).obj N))

/-- An initial signature with no axioms is the actual initial semantic theory. -/
def emptyTheory_isInitial (S₀ : Sign) (hS₀ : IsInitial S₀) :
    IsInitial (⟨S₀, ∅⟩ : Spec I) :=
  IsInitial.ofUniqueHom
    (fun T => ⟨hS₀.to T.sig, fun _ h => False.elim h⟩)
    (fun T f => Spec.hom_ext (hS₀.hom_ext f.sig (hS₀.to T.sig)))

/-- The source's initial-module constraint has exactly initial models,
with its unique-reduct-hom premise discharged from original exactness. -/
theorem initialConstraint_sat_iff (hExact : SemanticModels.Exact I)
    (T₀ T : Spec I) (hT₀ : IsInitial T₀) (H : T₀ ⟶ T)
    (M : SemanticModels.Models I T) :
    Sat I M.obj (⟨T₀, T, H, 𝟙 T.sig⟩ : Constraint I T.sig) ↔ Nonempty (IsInitial M) := by
  unfold Sat
  rw [I.map_id]
  constructor
  · rintro ⟨_, h⟩
    exact (freeAt_from_initialTheory_iff I hExact T₀ T hT₀ H M).1 h
  · intro h
    exact ⟨M.property, (freeAt_from_initialTheory_iff I hExact T₀ T hT₀ H M).2 h⟩

/-- In particular, the empty theory over an actual initial signature gives the
unparameterized module semantics described after Definition 4.14. -/
theorem initialSignatureConstraint_sat_iff (hExact : SemanticModels.Exact I)
    (S₀ : Sign) (hS₀ : IsInitial S₀) (T : Spec I)
    (H : (⟨S₀, ∅⟩ : Spec I) ⟶ T) (M : SemanticModels.Models I T) :
    Sat I M.obj (⟨⟨S₀, ∅⟩, T, H, 𝟙 T.sig⟩ : Constraint I T.sig) ↔ Nonempty (IsInitial M) :=
  initialConstraint_sat_iff I hExact _ T (emptyTheory_isInitial I S₀ hS₀) H M

end
end Silmaril.Logic.Institution.Structured.Constraints
