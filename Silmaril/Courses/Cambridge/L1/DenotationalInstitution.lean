module

public import Silmaril.Courses.Cambridge.L1.Denotational
public import Silmaril.Courses.Cambridge.L1.OperationalInstitution
public import Silmaril.Logic.Fragments.Institution.Thms

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.DenotationalInstitution

open CategoryTheory Silmaril.Logic.Fragments Silmaril.Semantics.Operational
open Denotational

/-- An atom names a read-only source and a proposed full return configuration. -/
def signature : AtomicSignature := ⟨{c : Config // ReadOnly c.expr} × Config⟩

/-- Denotational truth compares the computed value and the unchanged store. -/
def model : AtomicModel signature :=
  fun (source, target) =>
    denote source.val.expr source.val.store = some target.expr ∧ target.store = source.val.store

/-- Denotational satisfaction and the existing finite may observation agree. -/
theorem sat_iff (source : {c : Config // ReadOnly c.expr}) (target : Config) :
    (atomicInstitution.obj signature).Sat (Discrete.mk model) (source, target) ↔
      OperationalInstitution.semantics.May source.val (.returned target) :=
  (denote_eq_some_iff source.property).trans (OperationalInstitution.may_return_iff _ _).symm

end Silmaril.Courses.Cambridge.L1.DenotationalInstitution
