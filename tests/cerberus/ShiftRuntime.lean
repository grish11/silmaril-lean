module
public meta import Silmaril.Project.CompilesTo.Probe.Defs
public meta import Silmaril.Cerberus.Codec.WellFormed.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs

/-! Finite source executions with the actual pinned exported runtime. Only its
stdlib/impl maps are inputs: exported program functions and expected results are
never runtime bindings. This does not establish general runtime adequacy. -/
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes.C Silmaril.Project.CompilesTo

private def runtime : IO Functions.RuntimeInputs := do
  let process ← IO.Process.output {cmd := "gzip", args := #["-dc",
    "benchmarks/cerberus-elaboration/oracle/cast-sign-extend/core.sexp.gz"]}
  unless process.exitCode == 0 do throw <| IO.userError process.stderr
  let doc ← match Codec.WellFormed.parseDocument process.stdout with
    | .ok doc => pure doc
    | .error error => throw <| IO.userError (reprStr error)
  return {stdlib := doc.bindings.stdlib, impl := doc.bindings.impl, aliases := []}

private def check (rt : Functions.RuntimeInputs) (text : String) (want : Int) (wantUB : Option UndefinedBehaviour := none) : IO Unit := do
  let ail ← match FrontendAil text with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  let bindings ← match (Functions.elaborate
      Silmaril.Compiler.Native.TargetCoherence.linuxLP64 Target.emptyEnvironment rt ail
      ⟨⟨[]⟩, 100, 100000⟩).1 with
    | .ok value => pure value
    | .error error => throw <| IO.userError (reprStr error)
  let (_, body) := procParts bindings "f"
  let labels := Map.ofList (saves body).reverse
  let execution := run bindings.toFile ∅ 20000 ⟨.effectExpr body ∅, [.procedureReturn labels], {}⟩
  match wantUB, execution.ending with
  | none, some (.defined (.loaded (.specified (.integer got)))) =>
    unless got == want do throw <| IO.userError s!"expected {want}, got {got}"
  | some wanted, some (.ub _ got) =>
    unless got == wanted do throw <| IO.userError s!"expected {repr wanted}, got {repr got}"
  | _, ending => throw <| IO.userError s!"unexpected: {(observation ending).json.compress}"
  IO.println s!"PASS actual runtime left shift: {(observation execution.ending).json.compress}, transitions={execution.actions.length}"

public def main : IO Unit := do
  let rt ← runtime
  check rt "int f(void) { return 1 << 2; }" 4
  check rt "unsigned int f(void) { return 1u << 31; }" 2147483648
  check rt "int f(void) { return 1 << (0 - 1); }" 0 (some .UB051a_negative_shift)
  check rt "int f(void) { return 1 << 32; }" 0 (some .UB51b_shift_too_large)
  check rt "int f(void) { return (0 - 1) << 1; }" 0 (some .UB052a_negative_left_shift)
  check rt "int f(void) { return 1 << 31; }" 0 (some .UB052b_non_representable_left_shift)
