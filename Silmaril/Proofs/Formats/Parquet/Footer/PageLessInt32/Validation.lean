module

public import Silmaril.Formats.Parquet.Footer.PageLessInt32.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Footer.PageLessInt32

open Silmaril.Formats Parquet Footer.PageLessInt32

theorem validate_framed {limits : Footer.Limits} {depth : Nat} {source : Bytes}
    {span : Footer.Span} {metadata : Footer.Metadata}
    (admitted : validate limits depth source span metadata = .ok ()) :
    Footer.validate span.start depth
      { metadata with rowGroups := metadata.rowGroups.filter (!isPageLess ·) } = .ok () := by
  cases strict : Footer.validate span.start depth
      { metadata with rowGroups := metadata.rowGroups.filter (!isPageLess ·) } with
  | ok accepted => cases accepted; rfl
  | error cause =>
    unfold validate at admitted
    split at admitted
    · contradiction
    · split at admitted
      · split at admitted
        · contradiction
        · simp [strict, Except.mapError, Bind.bind, Except.bind] at admitted
      · contradiction

theorem pageLess_zero {group : Footer.RowGroup} (empty : isPageLess group = true) :
    group.numRows = 0 ∧ group.totalByteSize = 0 := by
  cases columns : group.columns with
  | nil => simp [isPageLess, columns] at empty
  | cons first rest =>
    cases rest with
    | nil =>
      simp [isPageLess, columns, Bool.and_eq_true, and_assoc] at empty
      exact ⟨empty.1, empty.2.1⟩
    | cons other tail => simp [isPageLess, columns] at empty

end Silmaril.Proofs.Formats.Parquet.Footer.PageLessInt32
