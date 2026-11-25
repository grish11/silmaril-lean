module

public import Silmaril.Courses.Cambridge.L1.OperationalInstitution
public import Silmaril.Courses.Cambridge.L2.OperationalInstitution
public import Silmaril.Courses.Cambridge.L3.OperationalInstitution

/-! A conjunctive specification language for named full configurations of
Cambridge L1, L2 and L3. A catalogue interprets finite names in the chosen
course adapter and induces the usual operational model reduct. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.StepSpecification

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Operational Silmaril.Logic.Fragments

inductive Language where
  | l1 | l2 | l3
  deriving DecidableEq, Repr

def Language.Config : Language → Type
  | .l1 => L1.Config
  | .l2 => L2.Config
  | .l3 => L3.Config

/-- Fix the shared unit label and use the three existing operational models verbatim. -/
def Language.system (language : Language) : TransitionSystem :=
  ⟨⟨language.Config, Unit⟩, match language with
    | .l1 => L1.OperationalInstitution.system.model
    | .l2 => L2.OperationalInstitution.system.model
    | .l3 => L3.OperationalInstitution.system.model⟩

/-- The direct course step, over the adapter's full configurations. -/
def Language.Step : (language : Language) → language.Config → language.Config → Prop
  | .l1 => L1.Step
  | .l2 => L2.Step
  | .l3 => L3.Step

theorem Language.model_iff_step (language : Language) (source target : language.Config) :
    language.system.model (source, (), target) ↔ language.Step source target := by
  cases language
  · exact L1.OperationalInstitution.sat_iff source target
  · exact L2.OperationalInstitution.sat_iff source target
  · exact L3.OperationalInstitution.sat_iff source target

/-- A document declares its course language and the number of configuration names. -/
structure Context where
  language : Language
  slots : Nat

/-- Signature change sends names forwards within one course language. -/
structure Context.Hom (left right : Context) where
  sameLanguage : left.language = right.language
  slot : Fin left.slots → Fin right.slots

instance : Category Context where
  Hom := Context.Hom
  id _ := ⟨rfl, id⟩
  comp f g := ⟨f.sameLanguage.trans g.sameLanguage, g.slot ∘ f.slot⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

abbrev Context.shape (context : Context) : Signature := ⟨Fin context.slots, Unit⟩

/-- Configuration names form an ordinary operational signature with one label. -/
def nameSignatures : Context ⥤ Signature where
  obj := Context.shape
  map f := ⟨f.slot, id⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sentence language is the existing conjunction fragment of step atoms. -/
def operationalLogic : Signature ⥤ Room.{0, 0, 0} :=
  conjunctions.institution Signature.institution

def institution : Context ⥤ Room.{0, 0, 0} := nameSignatures ⋙ operationalLogic

abbrev Sentence (context : Context) := List context.shape.Edge

abbrev Catalogue (context : Context) := Fin context.slots → context.language.Config

/-- Interpret the finite names as actual configurations without changing labels. -/
def interpretation (context : Context) (catalogue : Catalogue context) :
    context.shape ⟶ context.language.system.shape := ⟨catalogue, id⟩

/-- Translate an entire conjunction and pull the target transition relation back
to the configuration names. This corridor works for every target edge model. -/
def translation (context : Context) (catalogue : Catalogue context) :
    institution.obj context ⟶ operationalLogic.obj context.language.system.shape :=
  operationalLogic.map (interpretation context catalogue)

def model (context : Context) (catalogue : Catalogue context) : (institution.obj context).Mod :=
  (translation context catalogue).mod.obj (Discrete.mk context.language.system.model)

def Holds (context : Context) (catalogue : Catalogue context) (sentence : Sentence context) : Prop :=
  (institution.obj context).Sat (model context catalogue) sentence

theorem satisfaction (context : Context) (catalogue : Catalogue context)
    (sentence : Sentence context) :
    (operationalLogic.obj context.language.system.shape).Sat
      (Discrete.mk context.language.system.model) ((translation context catalogue).sen sentence) ↔
      Holds context catalogue sentence :=
  (translation context catalogue).sat _ _

/-- A decoded conjunction is true precisely when each named course step is allowed. -/
theorem holds_iff (context : Context) (catalogue : Catalogue context) (sentence : Sentence context) :
    Holds context catalogue sentence ↔
      ∀ edge : context.shape.Edge, edge ∈ sentence → context.language.Step (catalogue edge.1) (catalogue edge.2.2) := by
  change (∀ edge : context.shape.Edge, edge ∈ sentence → context.language.system.model
    (catalogue edge.1, edge.2.1, catalogue edge.2.2)) ↔ _
  exact forall₂_congr fun edge _ => by
    have label : (edge.2.1 : Unit) = () := Subsingleton.elim _ _
    rw [label]
    exact context.language.model_iff_step _ _

end Silmaril.Courses.Cambridge.StepSpecification
