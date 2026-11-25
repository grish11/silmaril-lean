module

public import Silmaril.Courses.Cambridge.StepSpecification.Institution

/-! Conjunctions of finite may-return claims over the existing typed
configuration catalogues. A claim can request any return, or name the
complete returned configuration, including its store. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.ReturnSpecification

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Fragments
open Silmaril.Semantics.Operational
open StepSpecification (Context Catalogue Language)

inductive Claim (State : Type) where
  | mayReturn (source : State)
  | mayReturnTo (source target : State)
  deriving DecidableEq, Repr

def Claim.map {State Target : Type} (f : State → Target) : Claim State → Claim Target
  | .mayReturn source => .mayReturn (f source)
  | .mayReturnTo source target => .mayReturnTo (f source) (f target)

def Claim.observed {State : Type} (sem : OpSem State State) : Claim State → Prop
  | .mayReturn source => ∃ target, sem.May source (.returned target)
  | .mayReturnTo source target => sem.May source (.returned target)

/-- Use the observation views registered by the course adapters. -/
def semantics : (language : Language) → OpSem language.Config language.Config
  | .l1 => L1.OperationalInstitution.semantics
  | .l2 => L2.OperationalInstitution.semantics
  | .l3 => L3.OperationalInstitution.semantics

def isValue : (language : Language) → language.Config → Prop
  | .l1 => fun c => L1.IsValue c.expr
  | .l2 => fun c => L2.IsValue c.expr
  | .l3 => fun c => L3.IsValue c.expr

/-- A concrete finite course run ends in a value and keeps the final store. -/
def Returns (language : Language) (source target : language.Config) : Prop :=
  Relation.ReflTransGen language.Step source target ∧ isValue language target

theorem may_return_iff (language : Language) (source target : language.Config) :
    (semantics language).May source (.returned target) ↔ Returns language source target := by
  cases language
  · exact L1.OperationalInstitution.may_return_iff source target
  · exact L2.OperationalInstitution.may_return_iff source target
  · exact L3.OperationalInstitution.may_return_iff source target

def Claim.realized (language : Language) : Claim language.Config → Prop
  | .mayReturn source => ∃ target, Returns language source target
  | .mayReturnTo source target => Returns language source target

theorem Claim.observed_iff (language : Language) (claim : Claim language.Config) :
    claim.observed (semantics language) ↔ claim.realized language := by
  cases claim with
  | mayReturn source => exact exists_congr (may_return_iff language source)
  | mayReturnTo source target => exact may_return_iff language source target

abbrev signature (State : Type) : AtomicSignature := ⟨Claim State⟩

def nameSignatures : Context ⥤ AtomicSignature where
  obj context := signature (Fin context.slots)
  map f := ⟨Claim.map f.slot⟩
  map_id _ := AtomicSignature.Hom.ext (funext fun claim => by cases claim <;> rfl)
  map_comp _ _ := AtomicSignature.Hom.ext (funext fun claim => by cases claim <;> rfl)

def observationLogic : AtomicSignature ⥤ Room.{0, 0, 0} := conjunctions.atomic

def institution : Context ⥤ Room.{0, 0, 0} := nameSignatures ⋙ observationLogic

abbrev Sentence (context : Context) := List (Claim (Fin context.slots))

/-- The catalogue translates named endpoints and pulls the observation
predicate back to the slot language. Existential witnesses in the target
range over all full course configurations. -/
def translation (context : Context) (catalogue : Catalogue context) :
    institution.obj context ⟶ observationLogic.obj (signature context.language.Config) :=
  observationLogic.map ⟨Claim.map catalogue⟩

def observationModel (language : Language) :
    (observationLogic.obj (signature language.Config)).Mod :=
  Discrete.mk (Claim.observed (semantics language))

def model (context : Context) (catalogue : Catalogue context) : (institution.obj context).Mod :=
  (translation context catalogue).mod.obj (observationModel context.language)

def Holds (context : Context) (catalogue : Catalogue context) (sentence : Sentence context) : Prop :=
  (institution.obj context).Sat (model context catalogue) sentence

theorem satisfaction (context : Context) (catalogue : Catalogue context)
    (sentence : Sentence context) :
    (observationLogic.obj (signature context.language.Config)).Sat
      (observationModel context.language) ((translation context catalogue).sen sentence) ↔
      Holds context catalogue sentence :=
  (translation context catalogue).sat _ _

theorem holds_iff (context : Context) (catalogue : Catalogue context) (sentence : Sentence context) :
    Holds context catalogue sentence ↔
      ∀ claim ∈ sentence, (claim.map catalogue).realized context.language := by
  change (∀ claim ∈ sentence, (claim.map catalogue).observed (semantics context.language)) ↔ _
  exact forall₂_congr fun claim _ => (claim.map catalogue).observed_iff context.language

end Silmaril.Courses.Cambridge.ReturnSpecification
