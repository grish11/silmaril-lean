import Silmaril.Project.CompilesTo.Probe.Defs
import Silmaril.Cerberus.Core.Outcome.Defs

/-! Actual frontend/Core finite execution regressions. These do not prove
frontend adequacy or source-to-machine refinement. -/
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes.C Silmaril.Project.CompilesTo

private def check (text : String) (pointer : Mem.Concrete.Pointer) (want : Int) : IO Unit := do
  let ail ← match FrontendAil text with
    | .ok a => pure a
    | .error e => throw <| IO.userError s!"frontend: {e}"
  let bindings ← match ElabAil ail with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"Core: {repr e}"
  let (params, body) := procParts bindings "f"
  let [(symbol, _)] := params | throw <| IO.userError "one actual Core parameter required"
  let labels := Map.ofList (saves body).reverse
  let pointerType : Ctype := .mk [] (.pointer ⟨false, false, false⟩ (.mk [] .void))
  let memory : Mem.Concrete.State :=
    {nextId := 1, lastAddress := 4096, allocations := Map.ofList [(0, ⟨4096, 8, false, false, some pointerType, none, .UB064_modifying_const⟩)]}
  let memory ← match Mem.Concrete.storeTyped ∅ memory pointerType (.allocated 0 4096)
      (.pointer (.mk [] .void) pointer) with
    | .ok (_, m) => pure m
    | .error e => throw <| IO.userError s!"entry store: {repr e}"
  let environment := extendEnv [(symbol, .object (.pointer (.allocated 0 4096)))] ∅
  let start : State := ⟨.effectExpr body environment, [.procedureReturn labels], memory⟩
  let execution := run bindings.toFile ∅ 20000 start
  match execution.ending with
  | some (.defined (.loaded (.specified (.integer got)))) =>
    unless got == want do throw <| IO.userError s!"expected {want}, got {got}"
  | ending => throw <| IO.userError s!"unexpected: {(observation ending).json.compress}"
  IO.println s!"PASS null comparison result={want} transitions={execution.actions.length}"

def main : IO Unit := do
  let null : Mem.Concrete.Pointer := .null (.mk [] .void)
  let nonnull : Mem.Concrete.Pointer := .allocated 7 4096
  for text in ["int f(void *p) { return p == 0; }", "int f(void *p) { return 0 == p; }"] do
    check text null 1
    check text nonnull 0
  for text in ["int f(void *p) { return p != 0; }", "int f(void *p) { return 0 != p; }"] do
    check text null 0
    check text nonnull 1

private def elaborationContext : Silmaril.Cerberus.Elaboration.State.Context :=
  Silmaril.Cerberus.Elaboration.State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"

private def markedChild : Silmaril.Cerberus.Elaboration.State.ElabM Silmaril.Cerberus.Elaboration.Construction.Effect := do
  let _ ← Silmaril.Cerberus.Elaboration.State.freshDescription .none
  return Silmaril.Cerberus.Elaboration.Construction.pureEffect
    (Silmaril.Cerberus.Elaboration.Construction.unspecified
      (.mk [] (.pointer ⟨false, false, false⟩ (.mk [] .void))))

private def translated := Silmaril.Cerberus.Elaboration.State.run
  (Silmaril.Cerberus.Elaboration.NullPointers.compareNull
    Silmaril.Cerberus.Target.pinnedApple false .unknown
    (.mk [] (.pointer ⟨false, false, false⟩ (.mk [] .void))) markedChild) elaborationContext

-- Child consumes symbol100; three wrappers follow, with loaded binder101.
example : translated.2.freshness.next = 104 := by cbv
example : (match translated.1 with
  | .ok (.mk _ (.wseq (.mk _ (.base (some s, _))) _ _)) => some s.number
  | _ => none) = some 101 := by cbv

-- Preserve the actual unspecified fallback; do not turn it into false.
example : (match translated.1 with
  | .ok (.mk _ (.wseq _ _ (.mk _ (.case_ _ [_, (_, .mk _ (.pure p))])))) => some p
  | _ => none) = some (Silmaril.Cerberus.Elaboration.Construction.undefined .unknown
    (.UB_CERB004_unspecified .UB_unspec_equality_ptr_vs_NULL)) := by cbv

example : (Silmaril.Cerberus.Elaboration.State.run
  (Silmaril.Cerberus.Elaboration.NullPointers.compareNull
    {Silmaril.Cerberus.Target.pinnedApple with cheri := true} false .unknown
    (.mk [] (.pointer ⟨false, false, false⟩ (.mk [] .void))) markedChild)
  elaborationContext).1.isOk = false := by cbv
