module
public import Silmaril.Elf.Corpus.CjsonInsert.Source.Defs
import Silmaril.Proofs.Elf.Corpus.CjsonInsert.Source
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonInsert.Source.Elaboration
open Silmaril.Cerberus Silmaril.Cerberus.Core
theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.CjsonInsert.succeeds
def core : Codec.FileBindings := (Source.inputs.run Source.ail).toOption.get succeeds
/-- Actual four-definition closure. Missing signatures or bodies fail lookup;
all helper calls execute these genuine computed definitions. -/
def actual : Option (List (Sym × Ctype) × Core.Dynamics.EE) := do
  unless core.funs.length == 4 do none
  let (symbol, .procedure _ _ (.loaded .integer)
      [(array, .object .pointer), (index, .object .pointer), (item, .object .pointer)] body) ←
    Silmaril.Project.Shapes.C.procedureNamed core "cJSON_InsertItemInArray" | none
  let (_, info) ← core.funInfo.find? (fun entry => entry.1.key == symbol.key)
  let .mk _ (.basic (.integer (.signed .int))) := info.2.2.1 | none
  let [(some array', arrayType), (some index', indexType), (some item', itemType)] := info.2.2.2.1 | none
  unless array.key == array'.key && index.key == index'.key && item.key == item'.key &&
      !info.2.2.2.2.1 && !info.2.2.2.2.2 do none
  let .mk _ (.pointer _ (.mk _ (.struct arrayTag))) := arrayType | none
  let .mk _ (.pointer _ (.mk _ (.struct itemTag))) := itemType | none
  let .mk _ (.basic (.integer (.signed .int))) := indexType | none
  unless arrayTag.key == itemTag.key do none
  for name in ["get_array_item", "suffix_object", "add_item_to_array"] do
    let some _ := Silmaril.Project.Shapes.C.procedureNamed core name | none
  return ([(array,arrayType),(index,indexType),(item,itemType)],body)
end Silmaril.Elf.Corpus.CjsonInsert.Source.Elaboration
