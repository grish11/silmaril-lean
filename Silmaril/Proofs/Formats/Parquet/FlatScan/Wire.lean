module

public import Silmaril.Formats.Parquet.FlatScan.Defs
import all Silmaril.Formats.Parquet.FlatScan.Defs
public import Batteries.Data.List.Basic
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatScan

open Silmaril.Formats Parquet FlatScan

private theorem readFrame_wire {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {field : Field} {frame : Page.Frame} {remaining count : Nat}
    {advertised : List Int} {values : List (Option Int32)}
    (read : readFrame limits decoder source field frame remaining true false advertised 0 =
      .ok (count, values)) :
    frame.value.crc = none ∧ decoder field frame.value
      (Footer.fileBytes source frame.payload.start frame.payload.stop) = .ok values := by
  cases checked : checkPage (ε := ε) limits field frame.value true false advertised 0 with
  | error reason => simp [readFrame, checked, Bind.bind, Except.bind] at read
  | ok shape =>
    obtain ⟨size, nulls⟩ := shape
    have crc : frame.value.crc = none := by
      cases raw : frame.value.crc with
      | none => rfl
      | some word => simp [checkPage, raw, MonadExcept.throw, Bind.bind, Except.bind] at checked
    refine ⟨crc, ?_⟩
    have enough : ¬remaining < size := by
      intro small
      simp [readFrame, checked, small, MonadExcept.throw, Bind.bind, Except.bind] at read
    let body := Footer.fileBytes source frame.payload.start frame.payload.stop
    cases decoded : decoder field frame.value body with
    | error reason =>
      simp [readFrame, checked, enough, body, decoded, Except.mapError, Bind.bind, Except.bind] at read
    | ok slots =>
      have same : slots = values := by
        simp only [readFrame, checked, enough, body, decoded, Except.mapError, Bind.bind, Except.bind,
          ite_false] at read
        split at read <;> try contradiction
        split at read <;> try contradiction
        exact congrArg Prod.snd (Except.ok.inj read)
      rw [same]

private def step {ε : Type} (limits : Limits) (decoder : DecodePage ε) (source : Bytes)
    (field : Field) (advertised : List Int) (entry : Page.Frame × Nat)
    (state : Nat × Array (Option Int32)) :
    Except (ColumnFailure ε) (ForInStep (Nat × Array (Option Int32))) := do
  let (frame, index) := entry
  let (count, values) ←
    (readFrame limits decoder source field frame state.1 true false advertised 0).mapError
      (.atPage index frame.header.start)
  return .yield (state.1 - count, state.2 ++ values.toArray)

private theorem forIn_wire {ε : Type} (limits : Limits) (decoder : DecodePage ε)
    (source : Bytes) (field : Field) (advertised : List Int) (indexed : List (Page.Frame × Nat))
    {start finish : Nat × Array (Option Int32)}
    (run : forIn indexed start (step limits decoder source field advertised) = .ok finish) :
    ∃ pages, List.Forall₂ (fun entry values =>
      entry.1.value.crc = none ∧ decoder field entry.1.value
        (Footer.fileBytes source entry.1.payload.start entry.1.payload.stop) = .ok values)
      indexed pages ∧ finish.2.toList = start.2.toList ++ pages.flatten := by
  induction indexed generalizing start finish with
  | nil =>
    simp [Pure.pure, Except.pure] at run
    subst finish
    exact ⟨[], .nil, by simp⟩
  | cons entry indexed ih =>
    obtain ⟨frame, index⟩ := entry
    cases read : readFrame limits decoder source field frame start.1 true false advertised 0 with
    | error cause =>
      simp [List.forIn_cons, step, read, Except.mapError, Bind.bind, Except.bind] at run
    | ok page =>
      obtain ⟨count, values⟩ := page
      have tail : forIn indexed (start.1 - count, start.2 ++ values.toArray)
          (step limits decoder source field advertised) = .ok finish := by
        simpa [List.forIn_cons, step, read, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure] using run
      obtain ⟨pages, related, cells⟩ := ih tail
      exact ⟨values :: pages, .cons (readFrame_wire read) related, by
        simpa [List.append_assoc] using cells⟩

private theorem frameColumn_wire {ε : Type} {limits : Limits} {source : Bytes} {footerStart rows : Nat}
    {field : Field} {column : Footer.ColumnChunk} {frames : List Page.Frame}
    (parsed : frameColumn (ε := ε) none false 0 limits source footerStart field rows column = .ok frames) :
    ∃ span, Page.columnSpan footerStart column.metadata = some span ∧
      Page.readChunk limits.page source span = .ok frames := by
  simp only [frameColumn] at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  rename_i span located
  cases read : Page.readChunk limits.page source span with
  | error reason => simp [Except.mapError, read] at parsed
  | ok actual =>
    have same : actual = frames := by simpa [Except.mapError, read] using parsed
    exact ⟨span, located, same ▸ read⟩

theorem scanColumn_wire {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footerStart rows : Nat} {field : Field}
    {column : Footer.ColumnChunk} {result : ColumnValues rows}
    (scanned : scanColumn limits decoder source footerStart field rows column = .ok result) :
    ∃ span frames pages, Page.columnSpan footerStart column.metadata = some span ∧
      Page.readChunk limits.page source span = .ok frames ∧
      List.Forall₂ (fun frame values => frame.value.crc = none ∧ decoder field frame.value
        (Footer.fileBytes source frame.payload.start frame.payload.stop) = .ok values) frames pages ∧
      result.cells.toList = pages.flatten := by
  cases parsed : frameColumn (ε := ε) none false 0 limits source footerStart field rows column with
  | error reason =>
    simp [scanColumn, scanColumnCore, parsed, Except.mapError, Bind.bind, Except.bind] at scanned
  | ok frames =>
    obtain ⟨span, located, framed⟩ := frameColumn_wire parsed
    have reduced : ((do
        let finish ← forIn frames.zipIdx (rows, #[])
          (step limits decoder source field column.metadata.encodings)
        if finish.1 != 0 then throw (.column .pageCount)
        if sized : finish.2.size = rows then pure ⟨finish.2, sized⟩
        else throw (.column .pageCount) : Except (ColumnFailure ε) (ColumnValues rows)).mapError
        ColumnFailure.reason) = .ok result := by
      unfold step
      simpa only [scanColumn, scanColumnCore, parsed, Except.mapError, Bind.bind, Except.bind,
        Option.isNone] using scanned
    cases loop : forIn frames.zipIdx (rows, #[])
        (step limits decoder source field column.metadata.encodings) with
    | error cause => simp [loop, Except.mapError, Bind.bind, Except.bind] at reduced
    | ok finish =>
      obtain ⟨pages, related, cells⟩ := forIn_wire limits decoder source field _ _ loop
      have mapped : List.Forall₂ (fun frame values => frame.value.crc = none ∧ decoder field
          frame.value (Footer.fileBytes source frame.payload.start frame.payload.stop) = .ok values)
          (frames.zipIdx.map Prod.fst) pages := List.forall₂_map_left_iff.mpr related
      have exactCells : result.cells.toList = finish.2.toList := by
        simp only [loop, Bind.bind, Except.bind] at reduced
        split at reduced <;> try contradiction
        split at reduced <;> try contradiction
        exact (congrArg (fun v : ColumnValues rows => v.cells.toList) (Except.ok.inj reduced)).symm
      exact ⟨span, frames, pages, located, framed, by simpa using mapped,
        by simpa [cells] using exactCells⟩

end Silmaril.Proofs.Formats.Parquet.FlatScan
