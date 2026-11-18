module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArrayItem.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C
def externalInputSha256 : String := "e7947c9c9c6a7ce5418af0eb92128a17ca78018458166089192b6bdb40e35d54"
def text : String := include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/get-array-item/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/get-array-item/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/get-array-item/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/get-array-item/program.sexp")
def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[.pointer, .int32], some .pointer⟩
end Silmaril.Elf.Corpus.CjsonArrayItem.Source
