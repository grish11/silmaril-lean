module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs

/-! Exact byte-selected dependency closure from an actual GCC-preprocessed cJSON
translation unit, with its GNU default-visibility metadata retained. This is not
full-TU frontend acceptance: unrelated system-header syntax still rejects.
Preprocessing/build correspondence is external provenance, not an assumed
semantic refinement. The runtime is the actual pinned exported stdlib/impl;
its original fixture functions are not runtime inputs. See the public receipts.
External literal dependency checking must accompany promotion of this source closure. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonTypePredicates.Source
open Silmaril.Cerberus Silmaril.Project.CompilesTo Silmaril.Project.Shapes.C

/-- Generated dependency marker: the static input gate checks this against every external literal. -/
def externalInputSha256 : String := "5c402664d886493f08124896aa1cef0fdf8db90d8021ae23856a2e2f1545fc9f"

def text : String := include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/predicates/context.c"
set_option maxRecDepth 100000 in
def ail : Ail.TypedProgram := ail_program% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/predicates/typed-ail.sexp")
#guard (FrontendAil text).toOption.map Probe.ailText == some (Probe.ailText ail)
set_option maxRecDepth 100000 in
def runtimeDocument : Codec.Document := core_document% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/predicates/runtime.sexp")
set_option maxRecDepth 100000 in
def programDocument : Codec.Document := core_document% (include_str "../../../../../corpus/cjson/semantic-inputs/linux-x86_64/predicates/program.sexp")

def inputs : ElaborationInputs where
  target := Silmaril.Compiler.Native.TargetCoherence.linuxLP64
  types := Target.emptyEnvironment
  runtime := {stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl, aliases := []}
  freshness := ⟨⟨[]⟩, 100, 100000⟩

def core : Codec.FileBindings := {programDocument.bindings with
  stdlib := runtimeDocument.bindings.stdlib, impl := runtimeDocument.bindings.impl}
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[.pointer], some .int32⟩
def function (name : String) : CFn signature where
  file := core.toFile
  params := paramsOf core name
  body := (procParts core name).2
end Silmaril.Elf.Corpus.CjsonTypePredicates.Source
