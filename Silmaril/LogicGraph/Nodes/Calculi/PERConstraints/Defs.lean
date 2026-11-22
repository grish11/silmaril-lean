module

public import Silmaril.Calculi.PERConstraints.Examples.Thms
public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Project.Room.Defs

open CategoryTheory Silmaril.Calculi.PERConstraints Silmaril.Calculi.PERConstraints.Examples

silmaril institution calculi.per_constraints := Silmaril.Calculi.PERConstraints.bundled
silmaril room calculi.per_constraints.bool := Silmaril.Calculi.PERConstraints.Examples.booleanRoom

silmaril problem calculi.per_constraints.separation in calculi.per_constraints.bool (expect := SAT) :=
  Dictionary.toCNF separation

silmaril problem calculi.per_constraints.conflict in calculi.per_constraints.bool (expect := UNS) :=
  Dictionary.toCNF conflict

@[answers "calculi.per_constraints.separation" sat]
public theorem perConstraints_separation_answer :
    ∃ model : booleanRoom.Mod, booleanRoom.Sat model (Dictionary.toCNF separation) := by
  obtain ⟨model, holds⟩ := (Dictionary.sat_iff_cnf separation).mp separation_sat
  exact ⟨Discrete.mk model, holds⟩

@[answers "calculi.per_constraints.conflict" uns]
public theorem perConstraints_conflict_answer :
    ∀ model : booleanRoom.Mod, ¬booleanRoom.Sat model (Dictionary.toCNF conflict) :=
  fun model => (Dictionary.unsat_iff_cnf conflict).mp conflict_unsat (Discrete.as model)
