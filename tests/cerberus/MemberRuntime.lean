module

public meta import Silmaril.Project.CompilesTo.Probe.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs

/-! Actual struct-pointer C frontend → typed Ail → Core finite execution cases. This is not
frontend adequacy or a C-to-ELF proof. Expected results are never runtime bindings. -/
public meta section

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes.C Silmaril.Project.CompilesTo

private def check (value : Int) : IO Unit := do
  let text := "struct S { int value; }; int f(struct S *p) { return p->value; }"
  let ail ← match FrontendAil text with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"frontend: {error}"
  let bindings ← match ElabAil ail with
    | .ok value => pure value
    | .error error => throw <| IO.userError s!"Core: {repr error}"
  let (params, body) := procParts bindings "f"
  let [(symbol, _)] := params | throw <| IO.userError "expected one pointer parameter"
  let [(tag, _)] := bindings.tagDefs | throw <| IO.userError "expected one struct definition"
  let aggregate : Ctype := .mk [] (.struct tag)
  let pointer : Ctype := .mk [] (.pointer ⟨false, false, false⟩ aggregate)
  let intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
  let memory : Mem.Concrete.State :=
    {nextId := 2, lastAddress := 8192, allocations := Map.ofList
      [(0, ⟨4096, 8, false, false, some pointer, none, .UB064_modifying_const⟩),
       (1, ⟨8192, 4, false, false, some aggregate, none, .UB064_modifying_const⟩)]}
  let tags := bindings.toFile.tagDefs
  let memory ← match Mem.Concrete.storeTyped tags memory pointer (.allocated 0 4096)
      (.pointer aggregate (.allocated 1 8192)) with
    | .ok (_, stored) => pure stored
    | .error error => throw <| IO.userError s!"pointer store: {repr error}"
  let memory ← match Mem.Concrete.storeTyped tags memory intType (.allocated 1 8192)
      (.integer (.signed .int) value) with
    | .ok (_, stored) => pure stored
    | .error error => throw <| IO.userError s!"member store: {repr error}"
  let environment := extendEnv [(symbol, .object (.pointer (.allocated 0 4096)))] ∅
  let labels := Map.ofList (saves body).reverse
  let execution := run bindings.toFile ∅ 20000 ⟨.effectExpr body environment, [.procedureReturn labels], memory⟩
  match execution.ending with
  | some (.defined (.loaded (.specified (.integer got)))) =>
      unless got == value do throw <| IO.userError s!"expected {value}, got {got}"
  | ending => throw <| IO.userError s!"unexpected: {(observation ending).json.compress}"
  IO.println s!"PASS pointer-member result={value} transitions={execution.actions.length}"

public def main : IO Unit := do
  check 37
  check (-19)
