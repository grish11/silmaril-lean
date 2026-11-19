module
public meta import Silmaril.Cerberus.Elaboration.LoopControl.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs
public meta import Silmaril.Cerberus.Codec.WellFormed.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Elaboration
open Silmaril.Project.Shapes.C

private def gotos (statement : Ail.TypedStatement) : List Sym :=
  let .mk _ _ _ node := statement
  match node with
  | .goto label => [label]
  | .block _ statements | .par statements => statements.attach.flatMap fun child => gotos child.val
  | .if_ _ yes no => gotos yes ++ gotos no
  | .while_ _ body _ | .do_ body _ _ | .switch _ body | .case_ _ body |
      .caseRangeGnu _ _ body | .default body | .label _ body _ | .marker _ body => gotos body
  | _ => []
termination_by sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have memberBound := List.sizeOf_lt_of_mem child.property
      omega

/-- A frontend/control regression, not a registered corpus problem or a source
adequacy theorem. Nested targets must not leak into the enclosing scope. -/
public def main : IO Unit := do
  let program ← match FrontendAil
      "int f(void) { int i=0; while(i) { while(i) { break; } continue; } return i; }" with
    | .ok value => pure value
    | .error why => throw <| IO.userError why
  let [(_, function)] := program.2.functionDefinitions | throw <| IO.userError "expected one function"
  let context := State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"
  let (result, after) := State.run (LoopControl.erase function.body) context
  let body ← match result with
    | .ok value => pure value
    | .error why => throw <| IO.userError (reprStr why)
  unless after.freshness.next == 104 do throw <| IO.userError "wrong nested label allocation count"
  let labels := LoopControl.collect body
  let expected : List Sym := [⟨⟨[]⟩,102,.none⟩,⟨⟨[]⟩,103,.none⟩,⟨⟨[]⟩,100,.none⟩,⟨⟨[]⟩,101,.none⟩]
  let generatedLabels := labels.filter fun entry => entry.1.digest == context.freshness.digest
  unless generatedLabels.map (fun entry => entry.1.key) == expected.map Sym.key &&
      labels.all (fun (_, visible) => visible.length == 1) do
    throw <| IO.userError s!"wrong lexical label scopes or insertion order {reprStr (labels.map fun (s,v) => (s.key, v.length))}"
  let expectedTargets : List Sym := [⟨⟨[]⟩,103,.none⟩] ++ gotos function.body
  unless (gotos body).map Sym.key == expectedTargets.map Sym.key do
    throw <| IO.userError s!"nested break/continue escaped their source target {reprStr ((gotos body).map Sym.key)}"
  for (label, visible) in labels do
    unless (LoopControl.lookup labels {label with description := .id "not identity"}).map List.length == some visible.length do
      throw <| IO.userError "label lookup used printed identity"
  let invalid := LoopControl.generated Loc.unknown (Ail.StatementNode.break_ : Ail.StatementNode Ail.GenTypeCategory)
  unless !(State.run (LoopControl.erase invalid) context).1.isOk do
    throw <| IO.userError "break outside loop accepted"
  let exhausted := {context with freshness := {context.freshness with maximum := 100}}
  let (result, stopped) := State.run (LoopControl.erase function.body) exhausted
  unless !result.isOk && stopped.freshness.next == 101 do
    throw <| IO.userError "freshness exhaustion lost consumed allocation"
  let runtimeBytes ← IO.Process.output {cmd := "gzip", args :=
    #["-dc", "benchmarks/cerberus-elaboration/oracle/cast-sign-extend/core.sexp.gz"]}
  unless runtimeBytes.exitCode == 0 do throw <| IO.userError runtimeBytes.stderr
  let runtime ← match Codec.WellFormed.parseDocument runtimeBytes.stdout with
    | .ok value => pure value
    | .error why => throw <| IO.userError (reprStr why)
  for (source, expected) in [
      ("int f(void) { int i=7; while(1) { int j=9; break; } return i; }", (7 : Int)),
      ("int f(void) { while(0) { return 1; } return 9; }", (9 : Int))] do
    let ail ← match FrontendAil source with
      | .ok value => pure value
      | .error why => throw <| IO.userError why
    let inputs : Functions.RuntimeInputs :=
      {stdlib := runtime.bindings.stdlib, impl := runtime.bindings.impl, aliases := []}
    let core ← match (Functions.elaborate Silmaril.Compiler.Native.TargetCoherence.linuxLP64
        Target.emptyEnvironment inputs ail ⟨⟨[]⟩, 100, 100000⟩).1 with
      | .ok value => pure value
      | .error why => throw <| IO.userError (reprStr why)
    let some (_, .procedure _ _ (.loaded .integer) [] body) := procedureNamed core "f"
      | throw <| IO.userError "actual no-argument integer function not found"
    let F : CFn ⟨[], some .int32⟩ := {file := core.toFile, params := [], body := body}
    let state : Core.Dynamics.State :=
      ⟨.effectExpr F.body ∅, [.procedureReturn F.bodyLabels], {}⟩
    let result := Core.Dynamics.run F.file ∅ 100000 state
    match result.ending with
    | some (.defined (.loaded (.specified (.integer got)))) =>
        unless got == expected do throw <| IO.userError s!"wrong actual while result {got}"
    | ending => throw <| IO.userError s!"actual while Core failed: {(Core.Dynamics.observation ending).json.compress}"
    let expectedObjects := if expected == 7 then 2 else 0
    unless result.finalState.memory.nextId == expectedObjects &&
        result.finalState.memory.dead.length == expectedObjects do
      throw <| IO.userError "while break/return did not end the actual local-object lifetimes"
  IO.println "PASS nested typed-Ail break/continue erasure, semantic label identity, lexical live-object scopes and freshness exhaustion; no corpus coverage counted"
