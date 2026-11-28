module

public import Silmaril.Formats.Parquet.Snapshot.Defs
import all Silmaril.Formats.Parquet.Snapshot.Defs

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot.PageLessInt32

open Silmaril.Formats Parquet Snapshot

theorem check_exact {limits : Limits} {input : Bytes} {snapshot : Checked}
    (opened : checkPageLessInt32 limits input = .ok snapshot) :
    Footer.readFooter limits.footer input = .ok (snapshot.footer, snapshot.metadata) ∧
      Footer.PageLessInt32.validate limits.footer limits.maxSchemaDepth input
        snapshot.footer snapshot.metadata = .ok () ∧ snapshot.bytes = input ∧
      snapshot.groupCount = snapshot.metadata.rowGroups.length ∧
      ∀ index, snapshot.groupAt index = snapshot.metadata.rowGroups[index]? := by
  cases footerRead : Footer.readFooter limits.footer input with
  | error cause => simp [checkPageLessInt32, footerRead, Except.mapError, Bind.bind, Except.bind] at opened
  | ok admitted =>
    obtain ⟨span, metadata⟩ := admitted
    cases valid : Footer.PageLessInt32.validate limits.footer limits.maxSchemaDepth input span metadata with
    | error cause =>
      simp [checkPageLessInt32, footerRead, valid, Except.mapError, Bind.bind, Except.bind] at opened
    | ok success =>
      cases success
      simp only [checkPageLessInt32, footerRead, valid, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure, Except.ok.injEq] at opened
      subst snapshot
      exact ⟨rfl, valid, rfl, by simp [Checked.groupCount], fun index => by simp [Checked.groupAt]⟩

end Silmaril.Proofs.Formats.Parquet.Snapshot.PageLessInt32
