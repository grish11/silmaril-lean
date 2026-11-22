module

public import Silmaril.Formats.PER.Dense.Defs
import Silmaril.Proofs.Formats.PER.Dense

public section

namespace Silmaril.Formats.PER.Dense

open Silmaril.Proofs.Formats

variable {Carrier Key Label : Type} {Row : Nat → Type}

theorem Index.injective (index : Index Carrier) : Function.Injective index.toNat := by
  intro first second same
  exact Option.some.inj ((index.read_write first).symm.trans (same ▸ index.read_write second))

theorem Index.toFin_some (index : Index Carrier) {size : Nat} {value : Carrier} {key : Fin size} :
    index.toFin? size value = some key ↔ index.toNat value = key.val := PERDense.toFin_some index

theorem Index.toFin_none (index : Index Carrier) (size : Nat) (value : Carrier) :
    index.toFin? size value = none ↔ size ≤ index.toNat value := PERDense.toFin_none index size value

theorem Index.fin_ofNat_none (size number : Nat) : (Index.fin size).ofNat? number = none ↔ size ≤ number :=
  Index.nat.toFin_none size number

theorem Index.uint32_ofNat_none (number : Nat) : Index.uint32.ofNat? number = none ↔ UInt32.size ≤ number :=
  Option.map_eq_none_iff.trans (Index.fin_ofNat_none _ _)

theorem Index.uint64_ofNat_none (number : Nat) : Index.uint64.ofNat? number = none ↔ UInt64.size ≤ number :=
  Option.map_eq_none_iff.trans (Index.fin_ofNat_none _ _)

theorem Index.fromFin_roundtrip (index : Index Carrier) {size : Nat} {key : Fin size} {value : Carrier}
    (read : index.fromFin? key = some value) : index.toFin? size value = some key :=
  index.toFin_some.mpr (index.write_read read)

theorem Index.toFin_roundtrip (index : Index Carrier) {size : Nat} {key : Fin size} {value : Carrier}
    (read : index.toFin? size value = some key) : index.fromFin? key = some value := by
  rw [Index.fromFin?, ← index.toFin_some.mp read, index.read_write]

theorem Table.read_at (table : Table Row) (key : Fin table.size) :
    table.read? key.val = some (table.at key) := List.getElem?_eq_getElem (table.length_eq.symm ▸ key.isLt)

theorem Table.read_none (table : Table Row) (key : Nat) : table.read? key = none ↔ table.size ≤ key := by
  rw [Table.read?, List.getElem?_eq_none_iff, table.length_eq]

theorem Table.readIndex_none (table : Table Row) (index : Index Carrier) (key : Carrier) :
    table.readIndex? index key = none ↔ table.size ≤ index.toNat key := table.read_none _

theorem Table.toMap_reads (table : Table Row) (key : Nat) : table.toMap.lookup? key = table.read? key :=
  PERDense.toMap_reads table key

theorem direct_eq_fibers (rows : List Label) : (Strategy.direct.per rows) = fibers (Table.ofList rows).read? := by
  change fibers (fun key => ((Table.ofList rows).read? key).bind some) = _
  exact congrArg fibers (funext fun key => by cases (Table.ofList rows).read? key <;> rfl)

theorem direct_dom (rows : List Label) (key : Nat) : (Strategy.direct.per rows).Dom key ↔ key < rows.length := by
  rw [direct_eq_fibers, fibers_dom, Option.isSome_iff_ne_none]
  exact (not_congr ((Table.ofList rows).read_none key)).trans Nat.not_le

theorem direct_toMap (rows : List Label) : fibers (Table.ofList rows).toMap.lookup? = Strategy.direct.per rows := by
  rw [direct_eq_fibers]
  exact congrArg fibers (funext (Table.ofList rows).toMap_reads)

theorem directOptional_toMap (rows : List (Option Label)) :
    fibers (fun key => ((Table.ofList rows).toMap.lookup? key).join) = Strategy.directOptional.per rows :=
  congrArg fibers (funext fun key => congrArg Option.join ((Table.ofList rows).toMap_reads key))

theorem completion_on_support (relation : PER Key) {left right : Key} (known : relation.Dom left) :
    (completion relation).r left right ↔ relation.rel left right :=
  ⟨fun hit => hit.elim (fun equal => equal ▸ known) id, Or.inr⟩

theorem completion_unknown (relation : PER Key) {left right : Key} (unknown : ¬ relation.Dom left) :
    (completion relation).r left right ↔ left = right :=
  ⟨fun hit => hit.elim id (fun edge => (unknown (relation.dom_left edge)).elim), Or.inl⟩

theorem pull_dom (relation : PER Carrier) (classify : Key → Option Carrier) (key : Key) :
    (relation.decodePull classify).Dom key ↔ ∃ value, classify key = some value ∧ relation.Dom value :=
  PERDense.pull_dom relation classify key

theorem onIndex_dom {size : Nat} (relation : PER (Fin size)) (index : Index Carrier) (key : Carrier) :
    (onIndex relation index).Dom key ↔ ∃ row, index.toNat key = row.val ∧ relation.Dom row := by
  rw [onIndex, pull_dom]
  simp only [index.toFin_some]

theorem pull_comp {Middle : Type} (relation : PER Carrier) (outer : Key → Option Middle)
    (inner : Middle → Option Carrier) :
    (relation.decodePull inner).decodePull outer = relation.decodePull (fun key => (outer key).bind inner) :=
  PERDense.pull_comp relation outer inner

end Silmaril.Formats.PER.Dense
