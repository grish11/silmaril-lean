module

public import Silmaril.Formats.PER.Naming.Defs
import Silmaril.Formats.PER.Thms

public section

namespace Silmaril.Proofs.Formats.PER

open Silmaril.Formats Silmaril.Semantics

variable {Name Repr : Type} {per : PER Repr} {rel : Naming.Relation Name Repr}

theorem mem_class_names {name : Name} (repr : {repr // per.Dom repr}) :
    name ∈ Naming.names (per.naming rel) (_root_.Quotient.mk per.supportSetoid repr) ↔
      ∃ otherRepr, name ∈ Naming.names rel otherRepr ∧ per.rel otherRepr repr.val := by
  classical
  constructor
  · rintro ⟨otherRepr, hit, projected⟩
    by_cases valid : per.Dom otherRepr
    · rw [Naming.graph, PER.projectClass, dite_eq_left valid] at projected
      exact ⟨otherRepr, hit, Quotient.exact (Option.some.inj projected)⟩
    · rw [Naming.graph, PER.projectClass, dite_eq_right valid] at projected
      cases projected
  · rintro ⟨otherRepr, hit, equivalent⟩
    have valid := per.dom_left equivalent
    refine ⟨otherRepr, hit, ?_⟩
    rw [Naming.graph, PER.projectClass, dite_eq_left valid]
    exact congrArg some (Quotient.sound equivalent)

end Silmaril.Proofs.Formats.PER
