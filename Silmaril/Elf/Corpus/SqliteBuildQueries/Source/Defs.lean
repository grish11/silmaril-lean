module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs

/-! Exact saved preprocessing spans for canonical SQLite 3.54.1 build queries.
The current host matches the recorded GCC version and requested build options;
this is not proof of canonical image/header identity or whole-TU adequacy.
The selected actual procedures have no globals or callees. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C

/-- Generated dependency marker: the static input gate checks this against every external literal. -/
def externalInputSha256 : String := "8b8baaf3b1d75220a6665d6fb4cfcf69f230ace0f629a15b62566603701cc780"

def text : String := include_str "../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/build-queries/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/build-queries/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/build-queries/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/build-queries/program.sexp")

def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩

def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[], some .int32⟩
end Silmaril.Elf.Corpus.SqliteBuildQueries.Source
