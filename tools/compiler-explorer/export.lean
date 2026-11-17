import Lean

/-!
# The compiler explorer's evidence exporter

    lake env lean --run tools/compiler-explorer/export.lean MANIFEST.json OUT.json

Reads a problem manifest (`silmaril.compiler-explorer.problem/1`), imports the Lean modules it
names (`lean.modules`, from the build Lake made), and decides the status of each obligation
*from the environment*, never from the manifest:

* `kernel`: the named declaration is a theorem, its type is the obligation's statement (the
  manifest's Lean term, elaborated here, compared up to reducible unfolding only), and its
  axioms are among `propext`, `Classical.choice` and `Quot.sound`. Theorems were checked by
  Lean's kernel when Lake built their modules; this tool reads them back from that build.
* `open`: the obligation names no declaration.
* `missing`, `not_theorem`, `mismatch`, `bad_axioms`, `elab_error`: the named declaration is
  absent, is not a theorem, proves another statement, depends on another axiom (`sorryAx`
  among them), or the statement does not elaborate. None of these is evidence.

The output records the manifest's SHA-256 (as given in the environment variable
`EXPLORER_MANIFEST_SHA256`, computed by the caller), the Lean version and the Git commit
(`EXPLORER_GIT_COMMIT`), so that the database can bind every status to the exact manifest and
build it was computed from.
-/

open Lean Meta Elab

namespace ExplorerExport

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure Obligation where
  id : String
  decl : Option String
  statement : String

def parseObligation (j : Json) : Except String Obligation := do
  let id ← j.getObjValAs? String "id"
  let statement ← j.getObjValAs? String "statement"
  let decl := (j.getObjValAs? String "decl").toOption
  return { id, decl, statement }

/-- Elaborate the statement and decide the status of one obligation. -/
def check (o : Obligation) : MetaM Json := do
  -- each obligation is elaborated with an empty message log: an error of one is not another's
  modifyThe Core.State fun st => { st with messages := {} }
  let base : List (String × Json) := [("id", Json.str o.id), ("statement", Json.str o.statement)]
  let st (s : String) : List (String × Json) := [("status", Json.str s)]
  let some declStr := o.decl
    | return Json.mkObj (base ++ st "open" ++ [("decl", Json.null)])
  let declName := declStr.toName
  let withDecl := base ++ [("decl", Json.str declStr)]
  let env ← getEnv
  let some ci := env.find? declName
    | return Json.mkObj (withDecl ++ st "missing")
  let .thmInfo _ := ci
    | return Json.mkObj (withDecl ++ st "not_theorem")
  let stx? := Parser.runParserCategory env `term o.statement
  let .ok stx := stx?
    | return Json.mkObj (withDecl ++ st "elab_error" ++
        [("detail", Json.str (match stx? with | .error e => e | .ok _ => ""))])
  let expected? ← (do
      let e ← Term.TermElabM.run' (do
        let e ← Term.elabTerm stx none
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e)
      if e.hasMVar || e.hasSorry || (← MonadLog.hasErrors) then return none
      return some e) <|> pure none
  let some expected := expected?
    | return Json.mkObj (withDecl ++ st "elab_error" ++
        [("detail", Json.str "the statement does not elaborate to a closed term")])
  let same ← withReducible (isDefEq ci.type expected)
  if (← IO.getEnv "EXPLORER_DEBUG").isSome && !same then
    IO.eprintln s!"{o.id}:\n  {ci.type}\n  {expected}"
  let axioms ← collectAxioms declName
  let axJson := Json.arr (axioms.map fun a => Json.str a.toString)
  let typeStr := toString (← ppExpr ci.type)
  let status :=
    if !same then "mismatch"
    else if axioms.all (allowedAxioms.contains ·) then "kernel"
    else "bad_axioms"
  return Json.mkObj (withDecl ++ st status ++ [("axioms", axJson), ("type", Json.str typeStr)])

unsafe def run (manifestPath outPath : String) : IO UInt32 := do
  let text ← IO.FS.readFile manifestPath
  let j ← IO.ofExcept (Json.parse text)
  let schema ← IO.ofExcept (j.getObjValAs? String "schema")
  unless schema == "silmaril.compiler-explorer.problem/1" do
    throw <| IO.userError s!"unexpected schema {schema}"
  let problemId ← IO.ofExcept (j.getObjValAs? String "id")
  let lean ← IO.ofExcept (j.getObjVal? "lean")
  let modules ← IO.ofExcept (lean.getObjValAs? (Array String) "modules")
  let obls ← IO.ofExcept (j.getObjValAs? (Array Json) "obligations")
  let obls ← IO.ofExcept (obls.mapM parseObligation)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<compiler-explorer>", fileMap := default }
  let ctx := { ctx with maxHeartbeats := 0 }
  let st : Core.State := { env }
  let (results, _) ← (obls.mapM check |>.run' {} {}).toIO ctx st
  let sha := (← IO.getEnv "EXPLORER_MANIFEST_SHA256").getD ""
  let commit := (← IO.getEnv "EXPLORER_GIT_COMMIT").getD ""
  let out := Json.mkObj [
    ("schema", Json.str "silmaril.compiler-explorer.evidence/1"),
    ("problem", Json.str problemId),
    ("manifest_sha256", Json.str sha),
    ("lean_version", Json.str Lean.versionString),
    ("git_commit", Json.str commit),
    ("modules", Json.arr (modules.map Json.str)),
    ("obligations", Json.arr results)]
  IO.FS.writeFile outPath (out.pretty ++ "\n")
  let bad := results.filter fun r =>
    match r.getObjValAs? String "status" with
    | .ok s => s != "kernel" && s != "open"
    | .error _ => true
  IO.println s!"{problemId}: {results.size} obligations, {bad.size} not evidence"
  return 0

end ExplorerExport

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [m, o] => ExplorerExport.run m o
  | _ =>
    IO.eprintln "usage: lake env lean --run tools/compiler-explorer/export.lean MANIFEST OUT"
    return 2
