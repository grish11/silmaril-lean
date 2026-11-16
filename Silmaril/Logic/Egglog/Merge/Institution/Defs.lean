module

public import Silmaril.Logic.Egglog.Merge.Thms
public import Silmaril.Logic.Institution.Examples.Propositional

@[expose] public section
namespace Silmaril.Logic.Egglog.Merge.Institution
open CategoryTheory Silmaril.Logic.Institution

variable (Value : Type) [SemilatticeSup Value]

/-- A fixed semantic lattice is shared by the signatures. Named ground keys are
renamed arbitrarily; two source keys may be identified. -/
abbrev Signature := Type

/-- An ideal assigns accumulated semantic information to each named key. -/
structure Model (Key : Signature) : Type 1 where
  value : Key → Value

namespace Model
variable {Value} {Key Target : Signature}

/-- Actual model arrows increase the information at every key. No equality-only
replacement or engine-generated relation is used. -/
structure Hom (M N : Model Value Key) : Type where
  le : ∀ key, M.value key ≤ N.value key

instance (M N : Model Value Key) : Subsingleton (Hom M N) :=
  ⟨by intro f g; cases f; cases g; rfl⟩

instance : Category (Model Value Key) where
  Hom := Hom
  id _ := ⟨fun _ => le_rfl⟩
  comp f g := ⟨fun key => le_trans (f.le key) (g.le key)⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

def reduct (f : Key → Target) : Model Value Target ⥤ Model Value Key where
  obj M := ⟨M.value ∘ f⟩
  map h := ⟨fun key => h.le (f key)⟩

end Model

/-- A stable information assertion, not an exact lookup: the model's information
at key contains the requested lattice lower bound. -/
structure Bound (Key : Signature) where
  key : Key
  lower : Value

namespace Bound
variable {Value} {Key Target : Signature}

def Holds (M : Model Value Key) (a : Bound Value Key) : Prop := a.lower ≤ M.value a.key

def map (f : Key → Target) (a : Bound Value Key) : Bound Value Target := ⟨f a.key, a.lower⟩

@[simp] theorem holds_map (f : Key → Target) (M : Model Value Target) (a : Bound Value Key) :
    (a.map f).Holds M ↔ a.Holds ((Model.reduct f).obj M) := Iff.rfl

theorem holds_hom {M N : Model Value Key} (h : M ⟶ N) (a : Bound Value Key)
    (ha : a.Holds M) : a.Holds N := le_trans ha (h.le a.key)

end Bound

/-- Finite positive premises imply a lower bound; no head is an integrity
constraint. A zero-premise present head is a fact. -/
structure Rule (Key : Signature) where
  body : List (Bound Value Key)
  head : Option (Bound Value Key)

namespace Rule
variable {Value} {Key Target : Signature}

def Holds (M : Model Value Key) (r : Rule Value Key) : Prop :=
  (∀ a ∈ r.body, a.Holds M) → r.head.elim False (Bound.Holds M)

def map (f : Key → Target) (r : Rule Value Key) : Rule Value Target :=
  ⟨r.body.map (Bound.map f), r.head.map (Bound.map f)⟩

end Rule

/-- Rules and positive ground queries share the actual ideal models. Keys stand
for normalized ground table inputs; no term frontend is assumed. -/
inductive Sentence (Key : Signature) where
  | rule (r : Rule Value Key)
  | query (goals : List (Bound Value Key))

namespace Sentence
variable {Value} {Key Target : Signature}

def Holds (M : Model Value Key) : Sentence Value Key → Prop
  | .rule r => r.Holds M
  | .query goals => ∀ a ∈ goals, a.Holds M

def map (f : Key → Target) : Sentence Value Key → Sentence Value Target
  | .rule r => .rule (r.map f)
  | .query goals => .query (goals.map (Bound.map f))

end Sentence

end Silmaril.Logic.Egglog.Merge.Institution
