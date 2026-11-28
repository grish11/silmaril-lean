module

public import Silmaril.Machine.SQLite.TestCode.Defs

public section

namespace Silmaril.Machine.SQLite.TestCode

universe u v

theorem Fixture.check_iff {Input : Type u} {Observation : Type v} [DecidableEq Observation]
    (fixture : Fixture Input Observation) (run : Input → Observation) :
    fixture.check run = true ↔ fixture.Passes run :=
  decide_eq_true_iff

end Silmaril.Machine.SQLite.TestCode
