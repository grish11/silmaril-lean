module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs

/-! Exact saved-TU projection of the actual SQLite version array and pointer getter.
Actual static array initializer, array decay and pointer ABI; source/TU/build and
loader/interposition adequacy remain unproved. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteGlobalVersion.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C

/-- Generated dependency marker: the static input gate checks this against every external literal. -/
def externalInputSha256 : String := "8176f850bbc07d56e4592b3c768d8c944ea1e7c5a134f5f06457025f0bce3be6"

def text : String := include_str "../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/global-version/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/global-version/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/global-version/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/global-version/program.sexp")

def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩

def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[], some .pointer⟩
end Silmaril.Elf.Corpus.SqliteGlobalVersion.Source
