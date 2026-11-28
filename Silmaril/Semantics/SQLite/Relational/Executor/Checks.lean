module

import Silmaril.Semantics.SQLite.Relational.Fragment.Thms

namespace Silmaril.SQLite.Relational.Checks

private abbrev fixture : Profile :=
  ⟨Unit, Unit, Bool, Unit, Unit, Unit, Nat, Bool, Nat⟩

private def reader : Executor fixture where
  resolve _ stmt := if stmt.source then .ok ⟨(), "v"⟩ else .error ()
  read
    | (file, true), (_, key) =>
      ⟨if key < 0 then .error () else .ok (some ()), file, true, []⟩
    | (file, false), (_, key) =>
      ⟨if key < 0 then .error () else .ok (some ()), file + 1, true, [file]⟩

private def start : Connection fixture where
  catalog := ()
  backing := 7
  cache := false
  exchanges := [5]
  session := ⟨false, 2, 3, -4⟩

private def atKey (key : Int64) : Invocation fixture.Ref :=
  ⟨⟨true⟩, some (1, key)⟩

-- A second successful call sees the cache filled by the first and emits no new read.
example :
    let after := { start with backing := 8, cache := true, exchanges := [5, 7] }
    let selected : SelectResult fixture.Value := ⟨"v", some ()⟩
    reader.executeBatch start [atKey 4, atKey 4] =
      (⟨[(selected, after), (selected, after)], none⟩, after) :=
  rfl

-- A failing cold read publishes its poststate and stops before the next invocation.
example :
    reader.executeBatch start [atKey (-4), atKey 4] =
      (⟨[], some (.run ())⟩, { start with backing := 8, cache := true, exchanges := [5, 7] }) :=
  rfl

-- Preparation precedes binding, and both failures leave the connection unchanged.
example :
    reader.execute start ⟨⟨false⟩, some (0, 4)⟩ = (.error (.prepare ()), start) ∧
    reader.execute start ⟨⟨true⟩, some (-1, 4)⟩ = (.error (.bind .range), start) :=
  ⟨rfl, rfl⟩

example : reader.execute start ⟨⟨true⟩, none⟩ = (.ok ⟨"v", none⟩, start) := rfl

example : reader.check start (.unsupported "join") = (.unsupported "join", start) := rfl

end Silmaril.SQLite.Relational.Checks
