module
public import Silmaril.Elf.Corpus.MimallocOsGlobals.Source.Defs
public import Silmaril.Elf.Corpus.MimallocOsGlobals.Defs
import Silmaril.Proofs.Elf.Corpus.MimallocOsGlobals.Source
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsGlobals.Source.Elaboration
theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.MimallocOsGlobals.succeeds
/-- Actual successful Core, without a default body/state. -/
def core : Silmaril.Cerberus.Codec.FileBindings :=
  (Source.inputs.run Source.ail).toOption.get succeeds

/-- Look up the actual no-argument procedure and its typed function metadata.
Only Linux LP64 unsigned-long returns with zero formal parameters are admitted.
The actual frontend emits `(variadic=false, prototype=false)` for these
standalone definitions; retain that metadata rather than inventing a prototype.
Failure stays `none`; no default procedure body or ABI is supplied. -/
def actualBody (g : Getter) : Option Silmaril.Cerberus.Core.Dynamics.EE := do
  let (symbol, .procedure _ _ (.loaded .integer) [] body) ←
      Silmaril.Project.Shapes.C.procedureNamed core g.name | none
  let (_, info) ← core.funInfo.find? (fun entry => entry.1.key == symbol.key)
  let .mk _ (.basic (.integer (.unsigned .long))) := info.2.2.1 | none
  unless info.2.2.2.1.isEmpty && !info.2.2.2.2.1 && !info.2.2.2.2.2 do none
  return body
end Silmaril.Elf.Corpus.MimallocOsGlobals.Source.Elaboration
