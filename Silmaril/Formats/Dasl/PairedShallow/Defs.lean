module

public import Silmaril.Formats.Dasl.Resolve.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl

/-- Two spellings per link occurrence, with one shared object/blob tag and shape. -/
abbrev PairedShallow (Concrete Abstract : Type) := Shallow (Concrete × Abstract)

namespace PairedShallow

variable {Concrete Abstract : Type}

def concrete : PairedShallow Concrete Abstract → Shallow Concrete := Shallow.map Prod.fst
def abstract : PairedShallow Concrete Abstract → Shallow Abstract := Shallow.map Prod.snd

/-- Agreement is a caller-chosen relation on the two typed, tagged projections
of each link. It does not compare unrelated name types for equality. -/
def Agrees (tree : PairedShallow Concrete Abstract)
    (relates : Link Concrete → Link Abstract → Prop) : Prop :=
  ∀ ⦃link⦄, link ∈ tree.directLinks → relates (Link.map Prod.fst link) (Link.map Prod.snd link)

def AgreesBy (tree : PairedShallow Concrete Abstract) (names : Concrete → Abstract) : Prop :=
  tree.Agrees fun concrete abstract => Link.map names concrete = abstract

def ofConcrete (names : Concrete → Abstract) : Shallow Concrete → PairedShallow Concrete Abstract :=
  Shallow.map fun name => (name, names name)

def diagonal : Shallow Concrete → PairedShallow Concrete Concrete := ofConcrete id

/-- Validity checks finite expansion of the abstract projection, not the concrete
one. The input need not be independently stored under a root name. -/
def AbstractValid (tree : PairedShallow Concrete Abstract) (store : Store Abstract) : Prop :=
  store.Binding ∧ ∃ value, Expands store tree.abstract value

end PairedShallow
end Silmaril.Formats.Dasl
