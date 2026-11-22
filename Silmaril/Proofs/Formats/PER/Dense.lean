module

public import Silmaril.Formats.PER.Dense.Defs

public section

namespace Silmaril.Proofs.Formats.PERDense

open Silmaril.Formats PER Dense Silmaril.Semantics

variable {Carrier Key : Type} {Row : Nat → Type}

theorem toFin_some (index : Index Carrier) {size : Nat} {value : Carrier} {key : Fin size} :
    index.toFin? size value = some key ↔ index.toNat value = key.val := by
  constructor
  · intro hit; exact ((Index.fin size).write_read hit).symm
  · intro equal
    rw [Index.toFin?, equal]
    exact (Index.fin size).read_write key

theorem toFin_none (index : Index Carrier) (size : Nat) (value : Carrier) :
    index.toFin? size value = none ↔ size ≤ index.toNat value := by
  simp only [Index.toFin?, Index.fin]
  split <;> simp_all

theorem toMap_reads (table : Table Row) (key : Nat) : table.toMap.lookup? key = table.read? key := by
  rw [Table.toMap, OrderedMap.lookup_ofLookupOn]
  cases hit : table.read? key with
  | none => simp
  | some _ =>
    have bound := (List.getElem?_eq_some_iff.mp hit).choose
    exact ite_eq_left (Finset.mem_range.mpr (table.length_eq ▸ bound))

theorem pull_dom (relation : PER Carrier) (classify : Key → Option Carrier) (key : Key) :
    (relation.decodePull classify).Dom key ↔ ∃ value, classify key = some value ∧ relation.Dom value := by
  constructor
  · rintro ⟨first, second, left, right, edge⟩
    exact ⟨first, left, Option.some.inj (right.symm.trans left) ▸ edge⟩
  · rintro ⟨value, hit, edge⟩
    exact ⟨value, value, hit, hit, edge⟩

theorem pull_comp {Middle : Type} (relation : PER Carrier) (outer : Key → Option Middle)
    (inner : Middle → Option Carrier) :
    (relation.decodePull inner).decodePull outer = relation.decodePull (fun key => (outer key).bind inner) := by
  apply PER.ext
  intro left right
  constructor
  · rintro ⟨first, second, hl, hr, value, other, hv, ho, edge⟩
    exact ⟨value, other, by simp [hl, hv], by simp [hr, ho], edge⟩
  · rintro ⟨value, other, hl, hr, edge⟩
    obtain ⟨first, hf, hv⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨second, hs, ho⟩ := Option.bind_eq_some_iff.mp hr
    exact ⟨first, second, hf, hs, value, other, hv, ho, edge⟩

end Silmaril.Proofs.Formats.PERDense
