module

import Lean.Data.Json
import Silmaril.Formats.Hive.PartitionPath.Defs
meta import Silmaril.Formats.Hive.PartitionPath.Defs
meta import Lean.Data.Json

open Lean Silmaril.Formats.Hive.PartitionPath

private structure Fixture where
  path : String
  entries : Partition
  deriving FromJson

private structure ArrowFixture extends Fixture where
  canonical : Bool
  deriving FromJson

private structure Fixtures where
  arrow : Array ArrowFixture
  hive : Array Fixture
  deriving FromJson

private def checkParse (fixture : Fixture) : IO Unit :=
  match parse {} fixture.path with
  | .ok entries =>
    unless entries == fixture.entries do
      throw (IO.userError s!"{fixture.path}: got {repr entries}, expected {repr fixture.entries}")
  | .error err => throw (IO.userError s!"{fixture.path}: {repr err}")

private def checkRender (fixture : ArrowFixture) : IO Unit := do
  let path ← match render {} fixture.entries with
    | .ok path => pure path
    | .error err => throw (IO.userError s!"{fixture.path}: {repr err}")
  if fixture.canonical && path != fixture.path then
    throw (IO.userError s!"expected canonical path {fixture.path}, got {path}")
  checkParse { fixture.toFixture with path }

public def main : IO Unit := do
  let source ← IO.FS.readFile "tests/formats/hive-partition/fixtures.json"
  let fixtures : Fixtures ← IO.ofExcept (Json.parse source >>= fromJson?)
  for fixture in fixtures.arrow do
    checkParse fixture.toFixture
    checkRender fixture
  for fixture in fixtures.hive do
    checkParse fixture
  IO.println s!"Checked {fixtures.arrow.size} Arrow and {fixtures.hive.size} Hive path fixtures"
