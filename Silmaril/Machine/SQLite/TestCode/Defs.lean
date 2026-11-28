module

@[expose] public section

namespace Silmaril.Machine.SQLite.TestCode

universe u v

/-- One input and its independently specified expected observation. The caller
chooses the observation type, including any errors, traces, or poststate it
wants to compare. -/
structure Fixture (Input : Type u) (Observation : Type v) where
  input : Input
  expected : Observation

variable {Input : Type u} {Observation : Type v}

def Fixture.Passes (fixture : Fixture Input Observation) (run : Input → Observation) : Prop :=
  run fixture.input = fixture.expected

def Fixture.check [DecidableEq Observation] (fixture : Fixture Input Observation)
    (run : Input → Observation) : Bool :=
  decide (run fixture.input = fixture.expected)

end Silmaril.Machine.SQLite.TestCode
