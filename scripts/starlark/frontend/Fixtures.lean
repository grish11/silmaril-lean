module

import Lean.Data.Json
import Silmaril.Languages.Starlark.Frontend.Checks
meta import Silmaril.Languages.Starlark.Frontend.Checks
import Silmaril.Languages.Starlark.Frontend.Module.Checks
meta import Silmaril.Languages.Starlark.Frontend.Module.Checks
import Silmaril.Languages.Starlark.Frontend.Module.SpreadChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.SpreadChecks
import Silmaril.Languages.Starlark.Frontend.Module.ComputedCallChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.ComputedCallChecks
import Silmaril.Languages.Starlark.Frontend.Module.ReturnCallChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.ReturnCallChecks
import Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks
meta import Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks

open Lean Silmaril.Languages.Starlark.Frontend
open Silmaril.Languages.Starlark.Frontend.Module (Observation controls spreadControls computedCallControls returnCallControls)

private def moduleObservation (expected : Observation) : Json :=
  let (phase, want) := match expected with
    | .exportedInt value => ("publication", toString value)
    | .undefinedName name => ("validation", s!"undefined: {name}")
    | .missingArgument name => ("runtime", s!"missing 1 argument ({name})")
    | .multipleValues name => ("runtime", s!"multiple values for parameter {reprStr name}")
    | .duplicateKey name => ("runtime", s!"duplicate key: {reprStr name}")
    | .duplicateExplicitKeyword name => ("validation", s!"keyword argument {reprStr name} is repeated")
    | .requiredAfterDefault _ => ("validation", "required parameter may not follow optional")
    | .invalidStar => ("runtime", "argument after * must be iterable")
    | .invalidStarStar => ("runtime", "argument after ** must be a mapping")
    | .uninitializedGlobal name => ("runtime", s!"global variable {name} referenced before assignment")
  Json.mkObj [("phase", toJson phase), ("want", toJson want)]

private def loaderFixture (control : Silmaril.Languages.Starlark.Frontend.Module.Loader.Control) : Json :=
  let label := Silmaril.Languages.Starlark.Frontend.Module.Loader.label
  let producer := Silmaril.Languages.Starlark.Frontend.Module.Loader.producer
  let (phase, want, marker) := match control.expected with
    | .exportedInt value | .wrapperExportedInt value => ("publication", toString value, "")
    | .missingExport name => ("runtime", s!"name {name} not found in module {label}", "")
    | .wrapperArgumentError name => ("runtime", s!"missing 1 argument ({name})", "")
    | .lateLoad => ("runtime", s!"name absent not found in module {label}", "99")
    | .privateImport name => ("validation", s!"names with leading underscores are not exported: {name}", "")
    | .emptyLoad => ("parse", "load statement must import at least 1 symbol", "")
    | .loadInFunction => ("validation", "load statement within a function", "")
  let wrapper := match control.expected with
    | .wrapperExportedInt _ => "relay"
    | _ => ""
  let loader := Json.mkObj [("phase", toJson phase), ("want", toJson want),
    ("marker", toJson marker), ("label", toJson label), ("producer", toJson producer), ("wrapper", toJson wrapper)]
  Json.mkObj [("name", toJson control.name), ("source", toJson control.source),
    ("accepts", toJson (phase != "parse")), ("loader", loader)]

public def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one fixture output path")
  let entries := fixtures.toArray.map fun fixture => Json.mkObj
    [("name", toJson fixture.name), ("source", toJson fixture.source),
     ("accepts", toJson fixture.goAccepts)]
  let modules := (controls ++ spreadControls ++ computedCallControls ++ returnCallControls).toArray.map fun control =>
    Json.mkObj [("name", toJson control.name), ("source", toJson control.source),
      ("accepts", toJson true), ("module", moduleObservation control.expected)]
  let loaders := Silmaril.Languages.Starlark.Frontend.Module.Loader.controls.toArray.map loaderFixture
  IO.FS.writeFile output (Json.arr (entries ++ modules ++ loaders)).compress
