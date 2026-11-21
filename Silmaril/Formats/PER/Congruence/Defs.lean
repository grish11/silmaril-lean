module
public import Mathlib.Order.Closure
public import Mathlib.Order.GaloisConnection.Basic
public import Silmaril.Formats.PER.Thms

@[expose] public section
namespace Silmaril.Formats.PER
variable {α : Type}

/-- A polynomial of constructor shapes and their (possibly empty) child positions.
Nonrecursive payloads belong to the shape and are compared by equality. -/
structure Constructors (α : Type) where
  Shape : Type
  Pos : Shape → Type
  make : (shape : Shape) → (Pos shape → α) → α
  enabled : (shape : Shape) → (Pos shape → α) → Prop

/-- Optional distinguished signature; algorithms and theorems also take explicit signatures. -/
class HasConstructors (α : Type) where
  constructors : Constructors α

namespace Constructors

def none (α : Type) : Constructors α where
  Shape := Empty
  Pos := Empty.elim
  make shape := shape.elim
  enabled shape := shape.elim

/-- Both tuples must be enabled, including the unique tuple of any nullary shape. -/
def Closed (C : Constructors α) (R : PER α) : Prop :=
  ∀ (shape : C.Shape) {left right : C.Pos shape → α},
    C.enabled shape left → C.enabled shape right →
    (∀ pos, R.rel (left pos) (right pos)) → R.rel (C.make shape left) (C.make shape right)

def Semantic (α : Type) [HasConstructors α] (R : PER α) : Prop :=
  (HasConstructors.constructors (α := α)).Closed R

/-- Least congruent PER, not a reflexive closure on the underlying type. -/
def generated (C : Constructors α) (R : PER α) : PER α :=
  PER.iInf fun S : {S : PER α // R ≤ S ∧ C.Closed S} => S.val

def upper (C : Constructors α) (R E : PER α) : Prop := E ≤ C.generated R

def SyntaxCompatible (C : Constructors α) (R E : PER α) : Prop :=
  R ≤ E ∧ C.upper R E ∧ ∀ x, E.Dom x

end Constructors
end Silmaril.Formats.PER
