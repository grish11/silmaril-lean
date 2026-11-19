module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArraySize.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C
def externalInputSha256 : String := "5e7fae6850a59fe3714c8da56750668fac0e1a78bdee5d0aa9e6619dfab1cf40"
def text : String := include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/get-array-size/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/get-array-size/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/get-array-size/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/get-array-size/program.sexp")
def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[.pointer], some .int32⟩
end Silmaril.Elf.Corpus.CjsonArraySize.Source
