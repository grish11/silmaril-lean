module

public meta import Silmaril.Project.CompilesTo.Probe.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs

/-! Actual C frontend → typed Ail → Core finite execution cases. This is not
frontend adequacy or a C-to-ELF proof. Expected results are never runtime bindings. -/
public meta section

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes.C Silmaril.Project.CompilesTo

private def check (text : String) (want : Int) (argument : Option Int := none) : IO Unit := do
  let ail ← match FrontendAil text with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"frontend: {error}"
  let bindings ← match ElabAil ail with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"Core: {repr error}"
  let (params, body) := procParts bindings "f"
  let (memory, environment) ← match params, argument with
    | [], none => pure ({}, ∅)
    | [(symbol, _)], some value => do
        let type : Ctype := .mk [] (.basic (.integer (.signed .int)))
        let memory : Mem.Concrete.State :=
          {nextId := 1, lastAddress := 4096, allocations := Map.ofList
            [(0, ⟨4096, 4, false, false, some type, none, .UB064_modifying_const⟩)]}
        let memory ← match Mem.Concrete.storeTyped ∅ memory type (.allocated 0 4096) (.integer (.signed .int) value) with
          | .ok (_, stored) => pure stored
          | .error error => throw <| IO.userError s!"entry store: {repr error}"
        pure (memory, extendEnv [(symbol, .object (.pointer (.allocated 0 4096)))] ∅)
    | _, _ => throw <| IO.userError "expected zero parameters or one allocated integer parameter"
  let labels := Map.ofList (saves body).reverse
  let execution := run bindings.toFile ∅ 20000 ⟨.effectExpr body environment, [.procedureReturn labels], memory⟩
  match execution.ending with
  | some (.defined (.loaded (.specified (.integer got)))) =>
      unless got == want do throw <| IO.userError s!"expected {want}, got {got}"
  | ending => throw <| IO.userError s!"unexpected: {(observation ending).json.compress}"
  IO.println s!"PASS bitwise result={want} transitions={execution.actions.length}"

public def main : IO Unit := do
  check "int f(void) { return 6 & 3; }" 2
  check "int f(void) { return 6 | 3; }" 7
  check "int f(void) { return 6 ^ 3; }" 5
  check "int f(int x) { return x & 255; }" 255 (some (-1))
  check "int f(int x) { return x | 3; }" (-5) (some (-8))
  check "int f(int x) { return x ^ 255; }" (-256) (some (-1))
  check "int f(void) { return (6 & 3) == 2; }" 1
