import Silmaril.Project.CompilesTo.Probe.Defs
import Silmaril.Cerberus.Core.Outcome.Defs

/-! Actual C frontend → Core LTS execution regressions. Selected signed overflow
reports UB; the same overflowing expression in an unselected branch is skipped.
These finite observations are not compiler adequacy or corpus semantic proofs. -/

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes.C
open Silmaril.Project.CompilesTo

private def check (text : String) (expected : Option Int) : IO Unit := do
  let ail ← match FrontendAil text with
    | .ok a => pure a
    | .error why => throw <| IO.userError s!"frontend: {why}"
  let bindings ← match ElabAil ail with
    | .ok b => pure b
    | .error why => throw <| IO.userError s!"elaboration: {repr why}"
  let body := (procParts bindings "f").2
  let labels := Map.ofList (saves body).reverse
  let start : State := {control := .effectExpr body ∅, stack := [.procedureReturn labels]}
  let execution := run bindings.toFile ∅ 20000 start
  match expected, execution.ending with
  | some want, some (.defined (.loaded (.specified (.integer got)))) =>
      unless got == want do throw <| IO.userError s!"expected {want}; got {got}"
  | none, some (.ub _ _) => pure ()
  | _, ending => throw <| IO.userError s!"unexpected ending: {(observation ending).json.compress}"
  IO.println s!"PASS {text} transitions={execution.actions.length}"

def main : IO Unit := do
  check "int f(void) { return 0 && (2147483647 + 1); }" (some 0)
  check "int f(void) { return 1 || (2147483647 + 1); }" (some 1)
  check "int f(void) { return 0 || 7; }" (some 1)
  check "int f(void) { return 1 && 7; }" (some 1)
  check "int f(void) { return 0 ? (2147483647 + 1) : 23; }" (some 23)
  check "int f(void) { return 1 ? 23 : (2147483647 + 1); }" (some 23)
  check "int f(void) { return 1 ? (2147483647 + 1) : 23; }" none
  check "int f(void) { return 1 && (2147483647 + 1); }" none
