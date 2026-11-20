module

public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Semantics.Naming

variable {Root Witness Name Obj Blob : Type}

/-- Collect the contributions of exactly the named witnesses in a presentation. -/
def collect (language : Relation Root Witness) (observe : Root → Witness → Relation Name Obj) :
    Relation Name Obj :=
  fun name payload => ∃ root witness, language root witness ∧ observe root witness name payload

namespace Stores

def collect (language : Relation Root Witness) (observe : Root → Witness → Stores Name Obj Blob) :
    Stores Name Obj Blob :=
  ⟨Naming.collect language (fun root witness => (observe root witness).objects),
    Naming.collect language (fun root witness => (observe root witness).blobs)⟩

/-- A common binding extension is possible. Neither side need already include the other. -/
def MergeCompatible (left right : Stores Name Obj Blob) : Prop := (left.union right).Binding

end Stores
end Silmaril.Semantics.Naming
