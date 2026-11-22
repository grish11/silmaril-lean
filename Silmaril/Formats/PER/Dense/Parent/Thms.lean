module

public import Silmaril.Formats.PER.Dense.Parent.Defs
import Silmaril.Proofs.Formats.PER.DenseParent

public section

namespace Silmaril.Formats.PER.Dense

open Silmaril.Proofs.Formats

variable {Row : Nat → Type} {Key : Type} {parent : Key → Option Key} {mode : Parent.Convention}

theorem Pointers.valid_iff (raw : Pointers Row) : raw.Valid ↔
    ∀ row ∈ raw.table.rows, ∀ target, raw.address row = some target → target < raw.table.size :=
  PERDenseParent.valid_iff raw

theorem Pointers.check_some_iff (raw : Pointers Row) : (raw.check?).isSome ↔ raw.Valid := by
  unfold check?
  split
  · exact ⟨fun _ => ‹raw.Valid›, fun _ => rfl⟩
  · constructor
    · intro impossible; cases impossible
    · exact fun valid => (‹¬ raw.Valid› valid).elim

theorem Pointers.observe_unknown (raw : Pointers Row) (key : Nat) :
    raw.observe key = .unknown ↔ raw.table.size ≤ key := PERDenseParent.observe_unknown raw key

theorem Pointers.observe_missing (raw : Pointers Row) (key : Fin raw.table.size) :
    raw.observe key.val = .missing ↔ raw.address (raw.table.at key) = none := PERDenseParent.observe_missing raw key

theorem Pointers.observe_edge (raw : Pointers Row) (source target : Fin raw.table.size) :
    raw.observe source.val = .edge target ↔ raw.address (raw.table.at source) = some target.val :=
  PERDenseParent.observe_edge raw source target

theorem Pointers.observe_invalid (raw : Pointers Row) (source target : Nat) : raw.observe source = .invalid target ↔
    ∃ row, raw.table.read? source = some row ∧ raw.address row = some target ∧ raw.table.size ≤ target :=
  PERDenseParent.observe_invalid raw source target

theorem Pointers.ofFin_valid (table : Table (fun size => Option (Fin size))) : (Pointers.ofFin table).Valid :=
  PERDenseParent.ofFin_valid table

theorem Pointers.ofFinTotal_valid (table : Table Fin) : (Pointers.ofFinTotal table).Valid := by
  apply (Pointers.valid_iff _).mpr
  exact fun row _ _ hit => (Option.some.inj hit) ▸ row.isLt

theorem Pointers.Checked.parent_none (checked : Checked Row) (key : Fin checked.val.table.size) :
    checked.parent key = none ↔ checked.val.address (checked.val.table.at key) = none :=
  PERDenseParent.parent_none checked key

theorem path_le_connectivity : Parent.partition mode parent ≤ Parent.connectivity parent :=
  PERDenseParent.partition_le_connectivity

theorem fixed_eq_connectivity (forest : Parent.FixedForest parent) :
    Parent.partition .fixedPoint parent = Parent.connectivity parent :=
  (PERDenseParent.connectivity_fixed forest).symm

theorem missing_eq_connectivity_on_keys (forest : Parent.MissingForest parent) :
    Parent.partition .terminalMissing parent = (Parent.connectivity parent).restrict (fun key => (parent key).isSome) :=
  (PERDenseParent.connectivity_eq_on_keys (fun key => (Parent.missing_dom forest key).mpr)).symm

theorem Pointers.Checked.normalized_direct (checked : Checked Row) (rooted : Rooted checked.parent) :
    checked.per .fixedPoint = checked.per .direct := Parent.fixed_flat rooted

theorem Pointers.Checked.normalize_preserves (checked : Checked Row) (view : ParentView)
    [DecidableRel (checked.per view).rel] : fibers (checked.normalize view).lookup? = checked.per view :=
  Partition.canonicalOn_partition _ _ fun _ _ => Finset.mem_univ _

theorem Pointers.Checked.normalize_lookup (checked : Checked Row) (view : ParentView)
    [DecidableRel (checked.per view).rel] (key root : Fin checked.val.table.size) :
    (checked.normalize view).lookup? key = some root ↔
      (checked.per view).rel key root ∧ ∀ other, (checked.per view).rel key other → root ≤ other :=
  Partition.canonicalOn_lookup_spec _ _ (fun _ _ => Finset.mem_univ _) key root

end Silmaril.Formats.PER.Dense
