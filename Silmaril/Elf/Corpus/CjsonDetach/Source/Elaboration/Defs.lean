module
public import Silmaril.Elf.Corpus.CjsonDetach.Source.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonDetach.Source
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonDetach.Source.Elaboration
open Silmaril.Cerberus Silmaril.Cerberus.Core
theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.CjsonDetach.succeeds
def core : Codec.FileBindings := (Source.inputs.run Source.ail).toOption.get succeeds
/-- Actual pointer-returning procedure, two pointer parameters and original function metadata.
No failed lookup is replaced by a default body, parameter or ABI. -/
def actual : Option (List (Sym × Ctype) × Core.Dynamics.EE) := do
  let (symbol, .procedure _ _ (.loaded .pointer) [(prev, .object .pointer), (item, .object .pointer)] body) ←
    Silmaril.Project.Shapes.C.procedureNamed core "cJSON_DetachItemViaPointer" | none
  let (_, info) ← core.funInfo.find? (fun entry => entry.1.key == symbol.key)
  let .mk _ (.pointer _ (.mk _ (.struct returnedTag))) := info.2.2.1 | none
  let [(some prev', prevType), (some item', itemType)] := info.2.2.2.1 | none
  unless prev.key == prev'.key && item.key == item'.key && !info.2.2.2.2.1 && !info.2.2.2.2.2 do none
  let .mk _ (.pointer _ (.mk _ (.struct parentTag))) := prevType | none
  let .mk _ (.pointer _ (.mk _ (.struct itemTag))) := itemType | none
  unless returnedTag.key == parentTag.key && itemTag.key == parentTag.key do none
  return ([(prev, prevType), (item, itemType)], body)
end Silmaril.Elf.Corpus.CjsonDetach.Source.Elaboration
