module

public import Silmaril.Calculi.PERConstraints.Defs
public import Silmaril.Formats.PER.Congruence.Defs

/-! The CNF constraint institution with models restricted to constructor-closed
PERs. Signature maps send enabled constructor applications to enabled ones. -/

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Congruence

open CategoryTheory Silmaril.Formats Silmaril.Logic.Institution

structure Signature where
  carrier : Syntax
  constructors : PER.Constructors carrier.Term

/-- Child positions are reindexed contravariantly, so a target tuple is obtained
by reading source children. No injectivity of the term function is required. -/
structure Signature.Hom (source target : Signature) where
  term : source.carrier.Term → target.carrier.Term
  shapeMap : source.constructors.Shape → target.constructors.Shape
  positionMap : ∀ shape, target.constructors.Pos (shapeMap shape) → source.constructors.Pos shape
  enabledMap : ∀ shape children, source.constructors.enabled shape children →
    target.constructors.enabled (shapeMap shape) (fun pos => term (children (positionMap shape pos)))
  makeMap : ∀ shape children, term (source.constructors.make shape children) =
    target.constructors.make (shapeMap shape) (fun pos => term (children (positionMap shape pos)))

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨id, id, fun _ => id, fun _ _ enabled => enabled, fun _ _ => rfl⟩
  comp first second :=
    ⟨second.term ∘ first.term, second.shapeMap ∘ first.shapeMap,
      fun shape pos => first.positionMap shape (second.positionMap (first.shapeMap shape) pos),
      fun shape children enabled => second.enabledMap _ _ (first.enabledMap shape children enabled),
      fun shape children => (congrArg second.term (first.makeMap shape children)).trans (second.makeMap _ _)⟩

def forget : Signature ⥤ Syntax where
  obj signature := signature.carrier
  map rename := ⟨rename.term⟩

abbrev Model (signature : Signature) :=
  {model : PER signature.carrier.Term // signature.constructors.Closed model}

/-- Both enabled premises transport, including for nullaries. -/
theorem closed_pull {source target : Signature} (rename : source ⟶ target)
    {model : PER target.carrier.Term} (closed : target.constructors.Closed model) :
    source.constructors.Closed (model.pull rename.term) := by
  intro shape left right hl hr related
  simpa only [PER.pull, rename.makeMap] using closed (rename.shapeMap shape)
    (rename.enabledMap shape left hl) (rename.enabledMap shape right hr) (fun pos => related (rename.positionMap shape pos))

def reduct {source target : Signature} (rename : source ⟶ target) (model : Model target) : Model source :=
  ⟨model.val.pull rename.term, closed_pull rename model.property⟩

def room (signature : Signature) : Room.{0,0,0} :=
  ⟨CNF signature.carrier.Term, Cat.of (Discrete (Model signature)),
    fun model sentence => CNF.Holds model.as.val sentence⟩

end Silmaril.Calculi.PERConstraints.Congruence
