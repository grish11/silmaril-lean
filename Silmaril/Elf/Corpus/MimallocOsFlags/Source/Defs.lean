module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs

/-! Exact saved-TU dependency closure from the canonical-matching mimalloc build.
This retains the real struct, global initializer and two read-only Boolean getter bodies. Full-TU frontend acceptance and global-startup correctness are not
claimed. The actual exported pinned stdlib/impl are the only runtime inputs. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsFlags.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C

/-- Generated dependency marker: the static input gate checks this against every external literal. -/
def externalInputSha256 : String := "caac41c256f40ef20abb49715d49ee60dffb6e60c6b0c33dc07c25aaeed2156d"

def text : String := include_str "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/os-flags/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/os-flags/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/os-flags/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/os-flags/program.sexp")

def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩

def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[], some .boolean⟩
end Silmaril.Elf.Corpus.MimallocOsFlags.Source
