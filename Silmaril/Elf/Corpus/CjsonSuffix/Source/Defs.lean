module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonSuffix.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C
def externalInputSha256 : String := "c1c8d2c1411a99de52a884fe2b3b00efe9a6084d33a5fa5b5d198bbb6a0daadf"
def text : String := include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/suffix-object/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/suffix-object/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/suffix-object/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/suffix-object/program.sexp")
def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[.pointer, .pointer], none⟩
end Silmaril.Elf.Corpus.CjsonSuffix.Source
