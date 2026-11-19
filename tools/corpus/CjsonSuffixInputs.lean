module
public meta import Silmaril.Project.CompilesTo.Probe.Defs
public meta import Silmaril.Cerberus.Codec.WellFormed.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Elaboration
open Silmaril.Project.Shapes.C Silmaril.Project.CompilesTo
private def document (b : Codec.FileBindings) : String :=
  Silmaril.Formats.SExpEncoding.printTagged (Codec.encodeDocument
    ⟨"b3e11ea334e95359907d4abf9194f0e7fedc6c6a", "explicit pinned exported runtime; Linux LP64 source projection", b, b.toFile, rfl, none⟩) ++ "\n"
public def main : IO Unit := do
  let root := "corpus/cjson/semantic-inputs/linux-x86_64/suffix-object/"
  let text ← IO.FS.readFile (root ++ "context.c")
  let result ← IO.Process.output {cmd := "gzip", args := #["-dc", "benchmarks/cerberus-elaboration/oracle/cast-sign-extend/core.sexp.gz"]}
  unless result.exitCode == 0 do throw <| IO.userError result.stderr
  let doc ← match Codec.WellFormed.parseDocument result.stdout with
    | .ok doc => pure doc
    | .error error => throw <| IO.userError (reprStr error)
  let ail ← match FrontendAil text with
    | .ok ail => pure ail
    | .error error => throw <| IO.userError error
  let runtime : Functions.RuntimeInputs := {stdlib := doc.bindings.stdlib, impl := doc.bindings.impl, aliases := []}
  let bindings ← match (Functions.elaborate Silmaril.Compiler.Native.TargetCoherence.linuxLP64
      Target.emptyEnvironment runtime ail ⟨⟨[]⟩, 100, 100000⟩).1 with
    | .ok bindings => pure bindings
    | .error error => throw <| IO.userError (reprStr error)
  IO.FS.writeFile (root ++ "typed-ail.sexp") (Probe.ailText ail)
  IO.FS.writeFile (root ++ "program.sexp") (document {bindings with stdlib := [], impl := []})
  IO.FS.writeFile (root ++ "runtime.sexp") (document {doc.bindings with
    main := none, tagDefs := [], globs := [], funs := [], extern := [], funInfo := [],
    loopAttributes := [], visibleObjects := []})
  IO.println s!"PASS actual source closure: {bindings.funs.length} Core functions, {bindings.globs.length} globals"
