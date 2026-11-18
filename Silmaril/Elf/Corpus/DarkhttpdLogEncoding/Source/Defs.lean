module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C
def externalInputSha256 : String := "876d0793d7a9a99898fd6efa4f232101231fb4f03b3851d742f3e4583f2b01d0"
def text : String := include_str "../../../../../corpus/darkhttpd/semantic-inputs/1.17/default/x86_64/O0/needs-logencoding/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/darkhttpd/semantic-inputs/1.17/default/x86_64/O0/needs-logencoding/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/darkhttpd/semantic-inputs/1.17/default/x86_64/O0/needs-logencoding/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/darkhttpd/semantic-inputs/1.17/default/x86_64/O0/needs-logencoding/program.sexp")
def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[.uint8], some .int32⟩
end Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Source
