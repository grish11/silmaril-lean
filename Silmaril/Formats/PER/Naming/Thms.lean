module

public import Silmaril.Formats.PER.Naming.Defs
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Formats.PER.Naming

public section

namespace Silmaril.Formats.PER

open Silmaril.Semantics

variable {Name Repr : Type} (per : PER Repr) {rel : Naming.Relation Name Repr}

theorem mem_class_names {name : Name} (repr : {repr // per.Dom repr}) :
    name ∈ Naming.names (per.naming rel) (_root_.Quotient.mk per.supportSetoid repr) ↔
      ∃ otherRepr, name ∈ Naming.names rel otherRepr ∧ per.rel otherRepr repr.val :=
  Proofs.Formats.PER.mem_class_names repr

theorem class_names_congr {left right : {repr // per.Dom repr}}
    (equivalent : per.rel left.val right.val) :
    Naming.names (per.naming rel) (_root_.Quotient.mk per.supportSetoid left) =
      Naming.names (per.naming rel) (_root_.Quotient.mk per.supportSetoid right) :=
  congrArg (Naming.names (per.naming rel)) (_root_.Quotient.sound equivalent)

theorem naming_binding (bound : Naming.Binding rel) : Naming.Binding (per.naming rel) :=
  bound.project per.projectClass

theorem naming_lookup (bound : Naming.Binding rel) (name : Name) :
    (per.naming_binding bound).lookup name = (bound.lookup name).bind per.projectClass :=
  bound.lookup_project per.projectClass name

end Silmaril.Formats.PER
