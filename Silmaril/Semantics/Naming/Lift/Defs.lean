module

public import Silmaril.Semantics.Naming.Defs

/-! Heterogeneous relation lifting. Coordinates choose their representations independently. -/

@[expose] public section

namespace Silmaril.Semantics.Naming.Lift

structure Coordinate where
  Surface : Type
  Meaning : Type
  represents : Relation Surface Meaning

def Coordinate.direct (Item : Type) : Coordinate := ⟨Item, Item, Eq⟩

def Coordinate.encoded {Surface Meaning : Type} (represents : Relation Surface Meaning) : Coordinate :=
  ⟨Surface, Meaning, represents⟩

/-- A name may have several representations, and a value may have several names. -/
def Coordinate.named {Name Repr Meaning : Type} (names : Relation Name Repr)
    (decodes : Relation Repr Meaning) : Coordinate :=
  .encoded (push names decodes)

def Tuple (types : List Type) : Type := match types with
  | [] => Unit
  | type :: rest => type × Tuple rest

abbrev Inputs (coordinates : List Coordinate) := Tuple (coordinates.map Coordinate.Surface)
abbrev Args (coordinates : List Coordinate) := Tuple (coordinates.map Coordinate.Meaning)

def Matches : (coordinates : List Coordinate) → Inputs coordinates → Args coordinates → Prop
  | [], _, _ => True
  | coord :: rest, (input, inputs), (arg, args) =>
      coord.represents input arg ∧ Matches rest inputs args

def rel {coordinates : List Coordinate} (predicate : Args coordinates → Prop) (inputs : Inputs coordinates) : Prop :=
  ∃ args, Matches coordinates inputs args ∧ predicate args

def where_ (coord : Coordinate) (predicate : coord.Meaning → Prop) : Set coord.Surface :=
  {input | rel (coordinates := [coord]) (fun args => predicate args.1) (input, ())}

end Silmaril.Semantics.Naming.Lift
