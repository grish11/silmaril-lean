import Lean

/-!
# The compiler explorer's evidence exporter

    lake build cexplorer-export
    lake env .lake/build/bin/cexplorer-export MANIFEST.json OUT.json

(`python3 -I tools/compiler-explorer/cexplorer.py verify DB MANIFEST…` runs it and ingests its
output; that is the only route by which the database records evidence as checked.)

Reads a problem manifest (`silmaril.compiler-explorer.problem/1`), imports the Lean modules it
names (`lean.modules`, from the build Lake made), and decides the status of each obligation
*from the environment*, never from the manifest:

* `kernel`: the named declaration is a theorem, its type is the obligation's statement (the
  manifest's Lean term, elaborated here, compared up to reducible unfolding only), and its
  axioms are among `propext`, `Classical.choice` and `Quot.sound`. Theorems were checked by
  Lean's kernel when Lake built their modules; this tool reads them back from that build.
* `refuted`: the obligation names a `refutation`, a theorem whose type is the negation of the
  statement (`¬ (statement)`), with the standard axioms.
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

def location (declName : Name) : MetaM Json := do
  let env ← getEnv
  let modName := (env.getModuleIdxFor? declName).bind fun index => env.header.moduleNames[index.toNat]?
  let line := ((← findDeclarationRanges? declName).map (·.range.pos.line)).getD 0
  return Json.mkObj [("module", toJson (modName.map Name.toString)), ("line", toJson line)]

unsafe def rendered (term : String) : MetaM String := do
  let stx ← ofExcept (Parser.runParserCategory (← getEnv) `term term)
  Term.TermElabM.run' (Term.evalTerm String (mkConst ``String) stx)

structure Obligation where
  id : String
  decl : Option String
  /-- A theorem claimed to prove the statement's negation. -/
  refutation : Option String
  statement : String

def parseObligation (j : Json) : Except String Obligation := do
  let id ← j.getObjValAs? String "id"
  let statement ← j.getObjValAs? String "statement"
  let decl := (j.getObjValAs? String "decl").toOption
  let refutation := (j.getObjValAs? String "refutation").toOption
  return { id, decl, refutation, statement }

/-- Elaborate the statement and decide the status of one obligation. -/
def check (o : Obligation) : MetaM Json := do
  -- each obligation is elaborated with an empty message log: an error of one is not another's
  modifyThe Core.State fun st => { st with messages := {} }
  let base : List (String × Json) := [("id", Json.str o.id), ("statement", Json.str o.statement)]
  let st (s : String) : List (String × Json) := [("status", Json.str s)]
  -- a proof (`decl`) of the statement, or a refutation: a proof of its negation
  let (declStr, negated) ← match o.decl, o.refutation with
    | some d, _ => pure (d, false)
    | none, some r => pure (r, true)
    | none, none => return Json.mkObj (base ++ st "open" ++ [("decl", Json.null)])
  let declName := declStr.toName
  let withDecl := base ++ [(if negated then "refutation" else "decl", Json.str declStr)]
  let env ← getEnv
  let some ci := env.find? declName
    | return Json.mkObj (withDecl ++ st "missing")
  let .thmInfo _ := ci
    | return Json.mkObj (withDecl ++ st "not_theorem")
  let stx? := Parser.runParserCategory env `term
    (if negated then "¬ (" ++ o.statement ++ ")" else o.statement)
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
    else if axioms.all (allowedAxioms.contains ·) then (if negated then "refuted" else "kernel")
    else "bad_axioms"
  -- where the declaration is written, for links to its source
  let loc ← location declName
  return Json.mkObj (withDecl ++ st status ++ [("axioms", axJson), ("type", Json.str typeStr),
    ("module", (loc.getObjVal? "module").toOption.getD Json.null),
    ("line", (loc.getObjVal? "line").toOption.getD Json.null)])

unsafe def run (current : IO.Ref (Option (Array String × Environment)))
    (manifestPath outPath sha : String) : IO UInt32 := do
  let text ← IO.FS.readFile manifestPath
  let j ← IO.ofExcept (Json.parse text)
  let schema ← IO.ofExcept (j.getObjValAs? String "schema")
  unless schema == "silmaril.compiler-explorer.problem/1" do
    throw <| IO.userError s!"unexpected schema {schema}"
  let problemId ← IO.ofExcept (j.getObjValAs? String "id")
  let lean ← IO.ofExcept (j.getObjVal? "lean")
  let modules ← IO.ofExcept (lean.getObjValAs? (Array String) "modules")
  let obls ← IO.ofExcept (j.getObjValAs? (Array Json) "obligations")
  -- obligations without a statement are unsupported: there is nothing to check
  let obls := obls.filter fun o => (o.getObjValAs? String "statement").toOption.isSome
  let obls ← IO.ofExcept (obls.mapM parseObligation)
  let env ← match ← current.get with
    | some (previous, env) => if modules == previous then pure (some env) else pure none
    | none => pure none
  let env ← match env with
    | some env => pure env
    | none =>
      enableInitializersExecution
      let env ← importModules (modules.map fun m => { module := m.toName }) {} (loadExts := true)
      current.set (some (modules, env))
      pure env
  let ctx : Core.Context := { fileName := "<compiler-explorer>", fileMap := default }
  let ctx := { ctx with maxHeartbeats := 0 }
  let st : Core.State := { env }
  let bindings := (lean.getObjValAs? (Array (String × String)) "bindings").toOption.getD #[]
  let definitions := (lean.getObjValAs? (Array String) "definitions").toOption.getD #[]
  let ((results, artifacts, locations), _) ← ((do
    let results ← obls.mapM check
    let artifacts ← bindings.mapM fun (role, term) => do return (role, Json.str (← rendered term))
    let locations ← definitions.mapM fun decl => do return (decl, ← location decl.toName)
    pure (results, artifacts, locations) : MetaM _) |>.run' {} {}).toIO ctx st
  let commit := (← IO.getEnv "EXPLORER_GIT_COMMIT").getD ""
  let out := Json.mkObj [
    ("schema", Json.str "silmaril.compiler-explorer.evidence/1"),
    ("problem", Json.str problemId),
    ("manifest_sha256", Json.str sha),
    ("lean_version", Json.str Lean.versionString),
    ("git_commit", Json.str commit),
    ("modules", Json.arr (modules.map Json.str)),
    ("artifacts", Json.mkObj artifacts.toList),
    ("definitions", Json.mkObj locations.toList),
    ("obligations", Json.arr results)]
  IO.FS.writeFile outPath (out.pretty ++ "\n")
  let bad := results.filter fun r =>
    match r.getObjValAs? String "status" with
    | .ok s => s != "kernel" && s != "open" && s != "refuted"
    | .error _ => true
  IO.println s!"{problemId}: {results.size} obligations, {bad.size} not evidence"
  -- a named proof that is not evidence fails the run (and CI)
  return if bad.isEmpty then 0 else 1

unsafe def batch (current : IO.Ref (Option (Array String × Environment))) : List String → IO UInt32
  | [] => pure 0
  | manifest :: out :: sha :: rest => do
    let status ← try run current manifest out sha catch error =>
      IO.eprintln s!"{manifest}: {error}"
      pure 1
    let next ← batch current rest
    pure (max status next)
  | _ => pure 2

end ExplorerExport

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let current ← IO.mkRef none
  match args with
  | [manifest, out] => ExplorerExport.run current manifest out ((← IO.getEnv "EXPLORER_MANIFEST_SHA256").getD "")
  | "--batch" :: jobs => ExplorerExport.batch current jobs
  | _ =>
    IO.eprintln "usage: lake env .lake/build/bin/cexplorer-export MANIFEST OUT"
    return 2
