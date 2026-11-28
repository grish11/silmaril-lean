module

import Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Check the original Coherence body in a projected module with the four
inputs it reads, directly and through a parsed INSTANCE host. -/

open Silmaril.Logic.Temporal.TLA Resolution DataElab

private def fromResult {α ε : Type} [Repr ε] : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def checkCoherence {signature : ExternalSignature} (term : Term signature .collections)
    (procId adrId noValId : BindingId) (cache : Term signature .collections → Bool) : IO Unit := do
  let .bounded _ (.quant .forall) [([.name p, .name q], .rigid proc), ([.name a], .rigid adr)]
      (.logic .implies (.mem true (.rigid noVal) (.enum [left, right])) (.eq false lhs rhs)) := term
    | throw (IO.userError s!"unexpected Coherence expansion: {reprStr term}")
  let reads := fun term who => match term with
    | .index _ (.index _ base (.witness first)) (.witness second) =>
      cache base && first == who && second == a
    | _ => false
  unless proc == procId && adr == adrId && noVal == noValId && p != q && p != a && q != a &&
      reads left p && reads right q && reads lhs p && reads rhs q do
    throw (IO.userError "unexpected Coherence domains or witness uses")

private def checkInstance (projected : Surface.Module) : IO Unit := do
  let host ← fromResult (Surface.Parser.parseModule "---- MODULE Host ----
CONSTANT Nodes, Adr, NoVal
VARIABLE view
C == INSTANCE CoherenceFixture WITH Proc <- Nodes, cache <- [node \\in Nodes |-> view[node]]
Out == C!Coherence
====")
  let checked ← fromResult (Resolution.Instances.check
    [("coherence", .parsed projected []), ("host", .parsed host [("CoherenceFixture", "coherence")])]
    "host")
  let some out := (checked.registry.moduleAt "host").bind (·.bindingAt (.ident "Out"))
    | throw (IO.userError "missing instance wrapper")
  let expanded ← fromResult (DataElab.Instances.lowerCollectionState checked (fun _ => none) 48 out.id)
  let constantId := fun i => BindingId.declared ⟨"host", [.unit 0, .member i]⟩
  let view := BindingId.declared ⟨"host", [.unit 1, .member 0]⟩
  let replacementSite : Site := ⟨"host", [.unit 2, .substitution 1]⟩
  checkCoherence expanded.term (constantId 0) (constantId 1) (constantId 2) fun
    | .function _ site binder slot (.rigid domain) (.index _ (.flexible base) (.witness use)) =>
      site == replacementSite && binder == .declared (site.child (.bound 0) |>.child (.binder 0)) &&
        domain == constantId 0 && base == view && slot == use
    | _ => false
  IO.println "WriteThroughCache.Coherence projection: INSTANCE replay checked the host graph at all four reads"

public def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "expected the pinned WriteThroughCache.tla path")
  let source ← fromResult (Surface.Parser.parseModule (← IO.FS.readFile file))
  unless source.name == "WriteThroughCache" &&
      source.extendsModules == ["Naturals", "Sequences", "MemoryInterface"] do
    throw (IO.userError "unexpected corpus module or imports")
  match Resolution.resolveWith .instanceSyntax [("pinned", .parsed source [])] "pinned" with
  | .error problem =>
    unless problem == ⟨⟨"pinned", [.import_ 0]⟩, .unresolvedImport "Naturals"⟩ do
      throw (IO.userError s!"unexpected whole-module diagnostic: {reprStr problem}")
  | .ok _ => throw (IO.userError "expected the intact module to require its EXTENDS inputs")
  let [unit] := source.units.filter (fun
    | .definition (.operator _ (.ident "Coherence" []) _) => true
    | _ => false)
    | throw (IO.userError "expected exactly one Coherence definition")
  let root := "coherence"
  let projected : Surface.Module := ⟨"CoherenceFixture", [],
    [.constants [(.ident "Proc" 0), (.ident "Adr" 0), (.ident "NoVal" 0)], .variables ["cache"], unit]⟩
  let registry ← fromResult (Resolution.resolve [(root, .parsed projected [])] root)
  let some defn := (registry.moduleAt root).bind (·.bindingAt (.ident "Coherence"))
    | throw (IO.userError "missing Coherence binding")
  let checked ← fromResult (Collections.lowerState registry [] (fun _ => none) 40 defn.id)
  unless defn.id == .declared ⟨root, [.unit 2]⟩ do
    throw (IO.userError "unexpected Coherence definition site")
  let constantId := fun i => BindingId.declared ⟨root, [.unit 0, .member i]⟩
  let cache := BindingId.declared ⟨root, [.unit 1, .member 0]⟩
  checkCoherence checked.term (constantId 0) (constantId 1) (constantId 2) fun
    | .flexible base => base == cache
    | _ => false
  IO.println "WriteThroughCache.Coherence: shared Proc bound, separate Adr bound, and all four cache reads checked"
  checkInstance projected
