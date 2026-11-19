module
public import Silmaril.Elf.Corpus.CjsonArrayItem.Source.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonArrayItem.Source
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArrayItem.Source.Elaboration
open Silmaril.Cerberus Silmaril.Cerberus.Core
theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.CjsonArrayItem.succeeds
def core : Codec.FileBindings := (Source.inputs.run Source.ail).toOption.get succeeds
/-- Both actual procedures and signatures are required; no failed lookup is
replaced by a default body. Core executes the helper in this actual file. -/
def actual : Option (List (Sym × Ctype) × Core.Dynamics.EE) := do
  let (symbol, .procedure _ _ (.loaded .pointer) [(array, .object .pointer), (index, .object .pointer)] body) ←
    Silmaril.Project.Shapes.C.procedureNamed core "cJSON_GetArrayItem" | none
  let (_, info) ← core.funInfo.find? (fun entry => entry.1.key == symbol.key)
  let .mk _ (.pointer _ (.mk _ (.struct returnedTag))) := info.2.2.1 | none
  let [(some array', arrayType), (some index', indexType)] := info.2.2.2.1 | none
  unless array.key == array'.key && index.key == index'.key && !info.2.2.2.2.1 && !info.2.2.2.2.2 do none
  let .mk _ (.pointer _ (.mk _ (.struct arrayTag))) := arrayType | none
  let .mk _ (.basic (.integer (.signed .int))) := indexType | none
  unless returnedTag.key == arrayTag.key do none
  let (helper, .procedure _ _ (.loaded .pointer) [(ha, .object .pointer), (hi, .object .pointer)] _) ←
    Silmaril.Project.Shapes.C.procedureNamed core "get_array_item" | none
  let (_, helperInfo) ← core.funInfo.find? (fun entry => entry.1.key == helper.key)
  let [(some ha', hat), (some hi', hit)] := helperInfo.2.2.2.1 | none
  let .mk _ (.pointer _ (.mk _ (.struct helperTag))) := hat | none
  let .mk _ (.pointer _ (.mk _ (.struct helperReturnTag))) := helperInfo.2.2.1 | none
  let .mk _ (.basic (.integer (.unsigned .long))) := hit | none
  unless ha.key == ha'.key && hi.key == hi'.key && helperTag.key == arrayTag.key &&
      helperReturnTag.key == arrayTag.key && !helperInfo.2.2.2.2.1 && !helperInfo.2.2.2.2.2 do none
  return ([(array, arrayType), (index, indexType)], body)
end Silmaril.Elf.Corpus.CjsonArrayItem.Source.Elaboration
