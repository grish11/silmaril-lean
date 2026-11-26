module

public import Silmaril.Formats.Parquet.Reader.Defs
import Silmaril.Proofs.Formats.Parquet.Reader
import Silmaril.Formats.Arrow.Events.Thms

/-! Full-consumption and logical scan laws for the typed row-group adapter. -/

public section

namespace Silmaril.Formats.Parquet.Reader

open Silmaril.Relational Silmaril.Formats.Arrow

variable {Group Id Kind Error : Type*} {Value : Kind → Type*} {schema : Scan.Schema Id Kind}

/-- Arrow emits one aligned batch per successful group in its source order. -/
theorem readAll_opened (source : Source Group schema Value Error) :
    readAll (.ok ⟨schema, source⟩) = .ok ⟨schema,
      ⟨(denoteGroups source.readGroup source.groups).1.map AlignedColumns.ofRows,
        (denoteGroups source.readGroup source.groups).2⟩⟩ :=
  Proofs.Formats.Parquet.Reader.readAll_opened source

/-- Full collection agrees with the row-group denotation, including open
failure and the ordered prefix before a read failure. -/
theorem collect_readAll (opened : OpenResult Group Id Value Error) :
    (readAll opened).collect = denote opened :=
  Proofs.Formats.Parquet.Reader.collect_readAll opened

/-- Logical selection and projection see the row-wise denotation. They carry
through its outcome, even when projection has zero columns or filtering keeps
zero rows before a failure. -/
theorem collect_scan_readAll (opened : OpenResult Group Id Value Error)
    (projection : (s : Scan.Schema Id Kind) → Scan.Projection s)
    (predicate : (s : Scan.Schema Id Kind) → Scan.Predicate s Value) :
    ((readAll opened).scan projection predicate).collect = (denote opened).map (fun observation =>
      let s := observation.table.schema
      ⟨⟨(projection s).schema, (projection s).scan (predicate s) observation.table.rows⟩,
        observation.termination⟩) := by
  rw [Events.EventStream.collect_scan, collect_readAll]

/-- Omitting a group is observationally sound for a fully consumed logical
scan if reading the omitted descriptor would succeed and its predicate keeps
no rows. The other descriptors still use the same decoder. This law gives a
premise for pruning adapters to prove from their own validation evidence. -/
theorem scan_readAll_skipGroup (source : Source Group schema Value Error)
    (before after : List Group) (group : Group)
    (projection : (s : Scan.Schema Id Kind) → Scan.Projection s)
    (predicate : (s : Scan.Schema Id Kind) → Scan.Predicate s Value)
    (split : source.groups = before ++ group :: after) {rows : RowGroup schema Value}
    (decoded : source.readGroup group = .ok rows)
    (rejected : ∀ row ∈ rows, (predicate schema row).getD false = false) :
    Events.EventStream.Equivalent
      ((readAll (.ok ⟨schema, source⟩)).scan projection predicate)
      ((readAll (.ok ⟨schema, { source with groups := before ++ after }⟩)).scan projection predicate) :=
  Proofs.Formats.Parquet.Reader.scan_readAll_skipGroup source before after group
    projection predicate split decoded rejected

end Silmaril.Formats.Parquet.Reader
