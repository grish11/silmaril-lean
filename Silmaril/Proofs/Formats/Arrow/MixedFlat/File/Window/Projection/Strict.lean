module

public import Silmaril.Formats.Arrow.MixedFlat.File.Window.Projection.Thms
import Silmaril.Formats.Arrow.FileReader.Thms
import Silmaril.Formats.Arrow.MixedFlat.File.Thms
import Silmaril.Formats.Arrow.MixedFlat.File.Window.Thms
import Silmaril.Prelude.Bytes.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window.Projection.Strict

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.File.Window

private theorem sameFooter {limits : Arrow.Limits} {input : KBytes}
    {strict : MixedFlat.File.Index input} {window : Index input 0 input.len}
    (strictRead : MixedFlat.File.readIndex limits input = .ok strict)
    (windowRead : readIndex limits input 0 input.len = .ok window) :
    strict.footer = window.footer := by
  have strictExact := MixedFlat.File.readIndex_exact strictRead
  have windowExact := readIndex_exact windowRead
  have strictTrailer := FileReader.readFooterSpan_verified
    (show FileReader.readFooterSpan limits input = .ok strict.span from by
      unfold MixedFlat.File.readIndex at strictRead
      cases spanRead : FileReader.readFooterSpan limits input with
      | error => simp [spanRead, bind, Except.bind, Except.mapError] at strictRead
      | ok span =>
        have spanExact : strict.span = span := by
          simp only [spanRead, Except.mapError, bind, Except.bind] at strictRead
          repeat' (split at strictRead <;> try contradiction)
          cases strictRead
          rfl
        simp [spanExact])
  let whole := input.slice 0 (input.len - 0)
  have wholeLen : whole.len = input.len := by simp [whole, KBytes.len_slice]
  have wholeBytes : whole.toList = input.toList := by
    change (input.slice 0 input.len).toList = input.toList
    rw [KBytes.toList_slice input 0 input.len strict.span.source (by simp), List.drop_zero,
      ← KBytes.length_toList input strict.span.source, List.take_length]
  have longEnough : 10 ≤ input.len := by have := strict.span.extent; omega
  have trailerFits : input.len - 10 + 4 ≤ input.len := by omega
  have trailerEqual : whole.read (whole.len - 10) 4 = input.read (input.len - 10) 4 := by
    have bound : whole.len - 10 + 4 ≤ whole.len := by simpa [wholeLen] using trailerFits
    rw [KBytes.read_eq whole _ _ window.span.source bound,
      KBytes.read_eq input _ _ strict.span.source trailerFits, wholeLen, wholeBytes]
  have lengthEqual : strict.span.length = window.span.length :=
    strictTrailer.2.2.2.1.symm.trans
      (trailerEqual.symm.trans (FileReader.readFooterSpan_verified windowExact.1).2.2.2.1)
  have startEqual : strict.span.start = window.footerStart := by
    have windowExtent : window.span.start + window.span.length + 10 = input.len :=
      window.span.extent.trans wholeLen
    have strictExtent := strict.span.extent
    simp only [Index.footerStart, Nat.zero_add]
    omega
  rw [startEqual, lengthEqual, windowExact.2.1] at strictExact
  exact (Except.ok.inj strictExact.1).symm

private theorem readAt_same {limits : MixedFlat.Limits} {input : KBytes}
    {strict : MixedFlat.File.Index input} {window : Index input 0 input.len}
    (footer : strict.footer = window.footer) (n : Nat)
    {observed : Option MixedFlat.Observed}
    (selected : strict.readAt limits n = .ok observed) :
    window.readAt limits n = .ok observed := by
  unfold MixedFlat.File.Index.readAt at selected
  rw [footer] at selected
  cases entry : window.footer.blocks[n]? with
  | none =>
    simp [Index.readAt, entry, Option.mapM, pure, Except.pure] at selected ⊢
    exact selected
  | some block =>
    cases record : MixedFlat.File.readRecord limits input window.footer.fields block with
    | error =>
      simp [entry, record, Option.mapM, Except.mapError, Functor.map, Except.map] at selected
    | ok result =>
      simpa [Index.readAt, entry, record, Option.mapM, Except.mapError, Functor.map, Except.map]
        using selected

theorem readProjectedAt_strict {limits : MixedFlat.Limits} {input : KBytes}
    {strict : MixedFlat.File.Index input} {window : Index input 0 input.len}
    (strictRead : MixedFlat.File.readIndex limits.observation.ipc input = .ok strict)
    (windowRead : readIndex limits.observation.ipc input 0 input.len = .ok window)
    {batches : List MixedFlat.Observed}
    (drained : strict.footer.blocks.mapM
      (MixedFlat.File.readRecord limits input strict.footer.fields) = .ok batches)
    (projection : Scan.Projection window.projectionSchema) (n : Nat) :
    match batches[n]? with
    | none => window.readProjectedAt limits n projection = .ok none
    | some batch =>
      ∃ output, window.readProjectedAt limits n projection = .ok (some output) ∧
        output.rowCount = batch.rowCount ∧ output.columns.length = projection.width ∧
        ∀ i : Fin projection.width, output.columns[i.val]? = batch.columns[(projection.index i).val]? := by
  have selected := readAt_same (sameFooter strictRead windowRead) n (strict.readAt_sequential drained n)
  cases entry : batches[n]? with
  | none => exact window.readProjectedAt_absent projection (by simpa [entry] using selected)
  | some batch => exact window.readProjectedAt_exact projection (by simpa [entry] using selected)

end Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Window.Projection.Strict
