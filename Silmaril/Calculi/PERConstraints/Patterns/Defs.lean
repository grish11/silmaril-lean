module

public import Silmaril.Calculi.PERConstraints.Congruence.Defs

/-! Typed constructor patterns on one syntax carrier. A sort selects a PER,
not a separate term grammar. DASL is the finite-branching instance. -/

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns

open CategoryTheory Silmaril.Formats Silmaril.Logic.Institution

inductive Pattern (base : Congruence.Signature) (Hole : Type) where
  | hole (index : Hole)
  | node (shape : base.constructors.Shape) (children : base.constructors.Pos shape → Pattern base Hole)

namespace Pattern

variable {base next : Congruence.Signature} {Hole : Type}

def plug (tuple : Hole → base.carrier.Term) : Pattern base Hole → base.carrier.Term
  | .hole index => tuple index
  | .node shape children => base.constructors.make shape (fun pos => plug tuple (children pos))

/-- Every internal node must be enabled at its plugged children. Holes do not
require constructor checks inside the substituted terms. -/
def Enabled (tuple : Hole → base.carrier.Term) : Pattern base Hole → Prop
  | .hole _ => True
  | .node shape children => base.constructors.enabled shape (fun pos => plug tuple (children pos)) ∧
      ∀ pos, Enabled tuple (children pos)

def map (rename : base ⟶ next) : Pattern base Hole → Pattern next Hole
  | .hole index => .hole index
  | .node shape children => .node (rename.shapeMap shape)
      (fun pos => map rename (children (rename.positionMap shape pos)))

end Pattern

structure Signature where
  base : Congruence.Signature
  Index : Type

/-- Universal rule satisfaction uses liftable tuples and exact guards. Child
positions must be covered so a translation cannot hide a disabled subpattern.
The term and sort maps need not be injective. -/
structure Signature.Hom (source target : Signature) where
  constructorMap : source.base ⟶ target.base
  indexMap : source.Index → target.Index
  ontoTerm : Function.Surjective constructorMap.term
  ontoPosition : ∀ shape, Function.Surjective (constructorMap.positionMap shape)
  reflectsEnabled : ∀ shape children,
    target.base.constructors.enabled (constructorMap.shapeMap shape)
      (fun pos => constructorMap.term (children (constructorMap.positionMap shape pos))) →
    source.base.constructors.enabled shape children

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨𝟙 _, id, Function.surjective_id, fun _ => Function.surjective_id, fun _ _ enabled => enabled⟩
  comp first second :=
    ⟨first.constructorMap ≫ second.constructorMap, second.indexMap ∘ first.indexMap,
      second.ontoTerm.comp first.ontoTerm,
      fun shape => (first.ontoPosition shape).comp (second.ontoPosition (first.constructorMap.shapeMap shape)),
      fun shape children enabled => first.reflectsEnabled shape children (second.reflectsEnabled _ _ enabled)⟩

def forget : Signature ⥤ Congruence.Signature where
  obj signature := signature.base
  map rename := rename.constructorMap

/-- A family of pre-semantic types, with no closure asserted. -/
abbrev Family (signature : Signature) := signature.Index → PER signature.base.carrier.Term

/-- All occurrences of one index share its assigned term and sort. Every
declared index supplies a premise, even when unused in the pattern. -/
structure Rule (signature : Signature) where
  arity : Nat
  holeSort : Fin arity → signature.Index
  output : signature.Index
  pattern : Pattern signature.base (Fin arity)

namespace Rule

variable {source target : Signature}

def Holds (rule : Rule source) (family : Family source) : Prop :=
  ∀ left right, rule.pattern.Enabled left → rule.pattern.Enabled right →
    (∀ index, (family (rule.holeSort index)).rel (left index) (right index)) →
    (family rule.output).rel (rule.pattern.plug left) (rule.pattern.plug right)

def map (rename : source ⟶ target) (rule : Rule source) : Rule target :=
  ⟨rule.arity, rename.indexMap ∘ rule.holeSort, rename.indexMap rule.output, rule.pattern.map rename.constructorMap⟩

end Rule

variable {source target : Signature}

def reduct (rename : source ⟶ target) (family : Family target) : Family source :=
  fun sort => (family (rename.indexMap sort)).pull rename.constructorMap.term

/-- A full constructor-congruent type gives a family by using the same PER
at every index. Full closure of unrelated PERs does not suffice. -/
def uniform (signature : Signature) (model : Congruence.Model signature.base) : Family signature :=
  fun _ => model.val

/-- A single selected semantic type at `output`, relative to the family
interpreting its hole types. Only selected rules with that output are tested. -/
def SemanticAt (rules : Set (Rule source)) (family : Family source) (output : source.Index) : Prop :=
  ∀ rule ∈ rules, rule.output = output → rule.Holds family

def Satisfies (rules : Set (Rule source)) (family : Family source) : Prop :=
  ∀ rule ∈ rules, rule.Holds family

def Extends (seed family : Family source) : Prop := ∀ sort, seed sort ≤ family sort

/-- Semantic intersection, not an executable saturation algorithm. All
components of an extending model are intersected over the same index set. -/
def generated (rules : Set (Rule source)) (seed : Family source) : Family source :=
  fun sort => PER.iInf fun model : {family : Family source // Extends seed family ∧ Satisfies rules family} =>
    model.val sort

def room (signature : Signature) : Room.{0,0,0} :=
  ⟨Rule signature, Cat.of (Discrete (Family signature)), fun model rule => rule.Holds model.as⟩

end Silmaril.Calculi.PERConstraints.Patterns
