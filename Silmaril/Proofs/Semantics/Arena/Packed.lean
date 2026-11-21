module

public import Silmaril.Semantics.Arena.Defs

public section

namespace Silmaril.Proofs.Semantics.Arena

open Silmaril.Semantics.Arena

variable {Name Payload : Type} {limit : Nat}

theorem read_ofFn (cells : Fin limit → Option (Slot Name Payload)) (index : Fin limit) :
    Dense.read ⟨Array.ofFn cells, Array.size_ofFn⟩ index = cells index := by
  simp [Dense.read]

theorem packExact_read (slots : { slots : Array (Slot Name Payload) // slots.size = limit }) (index : Nat) :
    (Dense.packExact slots).read index = slots.val[index]? := by
  cases hit : slots.val[index]? <;> simp [Dense.read, Dense.packExact, hit]

theorem packExact_noHoles (slots : { slots : Array (Slot Name Payload) // slots.size = limit }) :
    (Dense.packExact slots).NoHoles := by
  intro index
  have inside : index.val < slots.val.size := slots.property.symm ▸ index.isLt
  rw [packExact_read, Array.getElem?_eq_getElem inside]
  rfl

theorem read_packExact_unpack (arena : Dense limit Name Payload) (occupied : arena.NoHoles) (index : Nat) :
    (Dense.packExact (arena.unpack occupied)).read index = arena.read index := by
  rw [packExact_read]
  by_cases inside : index < limit
  · have inArray : index < (arena.unpack occupied).val.size := (arena.unpack occupied).property.symm ▸ inside
    rw [Array.getElem?_eq_getElem inArray]
    simpa only [Dense.unpack, Array.getElem_ofFn] using Option.some_get (occupied ⟨index, inside⟩)
  · have outside := Nat.le_of_not_gt inside
    rw [Array.getElem?_eq_none ((arena.unpack occupied).property.symm ▸ outside)]
    exact (arena.toBounded.property index outside).symm

theorem unpack_packExact (slots : { slots : Array (Slot Name Payload) // slots.size = limit }) :
    (Dense.packExact slots).unpack (packExact_noHoles slots) = slots := by
  apply Subtype.ext
  apply Array.ext_getElem?
  intro index
  rw [← packExact_read, read_packExact_unpack, packExact_read]

end Silmaril.Proofs.Semantics.Arena
