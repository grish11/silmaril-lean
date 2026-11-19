module
public import Silmaril.Elf.Corpus.CjsonArraySize.Source.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonArraySize.Source
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArraySize.Source.Elaboration
open Silmaril.Cerberus Silmaril.Cerberus.Core
theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.CjsonArraySize.succeeds
def core : Codec.FileBindings := (Source.inputs.run Source.ail).toOption.get succeeds
/-- Actual one-pointer Core parameter and pointer-to-struct source metadata.
A failed lookup remains none; no default body or substitute argument is used. -/
def actual : Option (List (Sym × Ctype) × Core.Dynamics.EE) := do
  let (symbol, .procedure _ _ (.loaded .integer) [(parameter, .object .pointer)] body) ←
    Silmaril.Project.Shapes.C.procedureNamed core "cJSON_GetArraySize" | none
  let (_, info) ← core.funInfo.find? (fun entry => entry.1.key == symbol.key)
  let .mk _ (.basic (.integer (.signed .int))) := info.2.2.1 | none
  let [(some parameter', type)] := info.2.2.2.1 | none
  unless parameter.key == parameter'.key && !info.2.2.2.2.1 && !info.2.2.2.2.2 do none
  let .mk _ (.pointer _ (.mk _ (.struct _))) := type | none
  return ([(parameter, type)], body)
end Silmaril.Elf.Corpus.CjsonArraySize.Source.Elaboration
