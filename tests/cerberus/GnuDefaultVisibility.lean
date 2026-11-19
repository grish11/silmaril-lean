module
public meta import Silmaril.Project.CompilesTo.Probe.Defs

/-! Narrow explicit grammar extension, not a pinned parser-equivalence claim.
GNU visibility is retained as metadata, never erased from the input source.
Other GNU annotations remain rejected. -/
public meta section
open Silmaril.Cerberus Silmaril.Project.Shapes.C
private def accepted : IO Unit := do
  let text := "__attribute__((visibility(\"default\"))) int f(void) { return 1; }"
  let ail ← match FrontendAil text with
    | .ok ail => pure ail
    | .error error => throw <| IO.userError error
  let [(_, function)] := ail.2.functionDefinitions
    | throw <| IO.userError "expected one actual function"
  let .mk [annotation] := function.attrs
    | throw <| IO.userError "visibility annotation was lost"
  unless annotation.ns.map (·.name) == some "gnu" && annotation.id.name == "visibility" &&
      (annotation.args.map fun (_, text, _) => text) == ["default"] do
    throw <| IO.userError s!"incorrect visibility metadata: {repr annotation}"
private def rejected (text : String) : IO Unit := do
  unless !(FrontendAil text).isOk do throw <| IO.userError "unsupported GNU annotation accepted"
public def main : IO Unit := do
  accepted
  rejected "__attribute__((visibility(default))) int f(void) { return 1; }"
  rejected "__attribute__((pure)) int f(void) { return 1; }"
  rejected "__attribute__((aligned(16))) int f(void) { return 1; }"
  rejected "__attribute__((visibility(\"hidden\"))) int f(void) { return 1; }"
  rejected "__attribute__((visibility(\"default\"), pure)) int f(void) { return 1; }"
  rejected "__attribute__((visibility(\"default\")) int f(void) { return 1; }"
  IO.println "PASS exact GNU default visibility metadata and six explicit rejections"
