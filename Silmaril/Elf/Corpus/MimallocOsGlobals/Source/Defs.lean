module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs

/-! Exact saved-TU dependency closure from the canonical-matching mimalloc build.
This retains the real struct, global initializer and two getter bodies, including
source calls. Full-TU frontend acceptance and global-startup correctness are not
claimed. The actual exported pinned stdlib/impl are the only runtime inputs. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsGlobals.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C

/-- Generated dependency marker: the static input gate checks this against every external literal. -/
def externalInputSha256 : String := "2b6b330ba584732803de11dbb89ff15117d0f1a105ee032d17869dafff1bb806"

def text : String := include_str "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/os-globals/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/os-globals/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/os-globals/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/os-globals/program.sexp")

def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩

def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[], some .uint64⟩
end Silmaril.Elf.Corpus.MimallocOsGlobals.Source
