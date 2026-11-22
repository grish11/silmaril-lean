module

public import Silmaril.Wasm.Wac.Dasl.Codec.Thms
public import Silmaril.Formats.Dasl.Resolve.Thms

public section

namespace Silmaril.Proofs.Wasm.Wac.Dasl

open Silmaril.Formats.Dasl
open Silmaril.Wasm.Wac Dasl

variable {Name Ref : Type} {store : Store Name}

private theorem inline_expands (item : Inline) :
    Expands store (embedInline item) (embedInline item) := by
  induction item with
  | ref impossible | obj impossible _ _ | blob impossible _ => exact impossible.elim
  | dict _ _ ih => exact .dict ih
  | list _ _ ih => exact .list ih
  | _ => constructor

private theorem pair_expands {left right : Shallow Name} {left' right' : Named Name} :
    Expands store (Encode.pairEntry.encode (left, right)) (Encode.pairEntry.encode (left', right')) ↔
      Expands store left left' ∧ Expands store right right' := by
  constructor
  · intro expanded
    cases expanded with
    | list hit => exact ⟨hit 0, hit 1⟩
  · rintro ⟨first, second⟩
    exact .list fun index => by
      by_cases zero : index.val = 0 <;> simp [zero, first, second]

private theorem list_map_node {Item : Type} (items : List Item) (map : Item → Tree Ref Name) :
    Encode.list.encode (items.map map) = .list items.length (fun index => map (items.get index)) := by
  change Tree.list (items.map map).length (items.map map).get = _
  have len : (items.map map).length = items.length := List.length_map map
  congr 1
  apply Function.hfunext (congrArg Fin len)
  intro low high index
  have same : low.val = high.val := Fin.val_eq_val_of_heq index
  simp [List.get_eq_getElem, same]

private theorem list_expands {Item : Type} (items : List Item) (low : Item → Shallow Name) (high : Item → Named Name) :
    Expands store (Encode.list.encode (items.map low)) (Encode.list.encode (items.map high)) ↔
      ∀ item ∈ items, Expands store (low item) (high item) := by
  rw [list_map_node, list_map_node]
  constructor
  · intro expanded item member
    obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
    cases expanded with
    | list hit => exact hit ⟨index, bound⟩
  · intro hits
    exact .list fun index => hits _ (List.getElem_mem _)

private theorem row_expands (row : PkgSig × (Name × ByteArray)) :
    Expands store
      ((pairCodec ((signature typeCodec).then inlineCodec) rawLink).encode (row.1, row.2.1))
      ((pairCodec ((signature typeCodec).then inlineCodec) rawBlob).encode row) ↔
    store.blobs row.2.1 row.2.2 := by
  change Expands store (Encode.pairEntry.encode (embedInline ((signature typeCodec).encode row.1), .ref (.blob row.2.1)))
      (Encode.pairEntry.encode (embedInline ((signature typeCodec).encode row.1), .blob row.2.1 row.2.2)) ↔ _
  rw [pair_expands]
  refine ⟨fun hit => ?_, fun hit => ⟨inline_expands _, .blob hit⟩⟩
  cases hit.2 with
  | blob stored => exact stored

theorem expansion_iff (value : Composition (Name × ByteArray)) :
    Expands store (shallow.encode value.names) (expanded.encode value) ↔
      ∀ row ∈ value.packages, store.blobs row.2.1 row.2.2 := by
  unfold shallow expanded codec composition
  change Expands store (Encode.pairEntry.encode (.string familyTag, Encode.pairEntry.encode
    (embedInline ((graph typeCodec sourceCodec).encode value.graph),
      (Encode.listOf (pairCodec ((signature typeCodec).then inlineCodec) rawLink)).encode value.names.packages)))
    (Encode.pairEntry.encode (.string familyTag, Encode.pairEntry.encode
    (embedInline ((graph typeCodec sourceCodec).encode value.graph),
      (Encode.listOf (pairCodec ((signature typeCodec).then inlineCodec) rawBlob)).encode value.packages))) ↔ _
  simp only [Encode.listOf_encode, Composition.names, List.map_map, Function.comp_def]
  rw [pair_expands, pair_expands, list_expands]
  exact ⟨fun hit row member => (row_expands row).1 (hit.2.2 row member),
    fun hits => ⟨.string _, inline_expands _, fun row member => (row_expands row).2 (hits row member)⟩⟩

theorem expanded_shallow (value : Composition (Name × ByteArray)) :
    (Named.embed (expanded.encode value)).shallow = shallow.encode value.names :=
  ((expansion_iff (store := ⟨fun _ _ => True, fun _ _ => True⟩) value).2 fun _ _ => trivial).shallow_eq

end Silmaril.Proofs.Wasm.Wac.Dasl
