module

public import Silmaril.Formats.PER.Defs
public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Formats.PER

open Silmaril.Semantics

variable {Name Repr : Type}

/-- Project only supported representations. An unsupported payload may still
have a raw store binding; it supplies no semantic value. -/
noncomputable def projectClass (per : PER Repr) (repr : Repr) : Option per.Quotient :=
  open Classical in
    if valid : per.Dom repr then some (_root_.Quotient.mk per.supportSetoid ⟨repr, valid⟩) else none

/-- The names of a supported class are contributed by all its named representatives. -/
noncomputable def naming (per : PER Repr) (rel : Naming.Relation Name Repr) :
    Naming.Relation Name per.Quotient := Naming.project rel per.projectClass

end Silmaril.Formats.PER
