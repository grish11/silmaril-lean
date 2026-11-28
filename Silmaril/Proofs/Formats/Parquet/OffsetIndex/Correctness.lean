module

public import Silmaril.Formats.Parquet.OffsetIndex.Defs
import all Silmaril.Formats.Parquet.OffsetIndex.Defs
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.ThriftCompact.Traversal.Thms
import Init.Data.ByteArray.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.OffsetIndex

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.OffsetIndex

public theorem readExact_ok_iff {limits : Limits} {bytes : Bytes} {locations : List Location} :
    readExact limits bytes = .ok locations ↔ readPrefix limits bytes = .ok (locations, bytes.length) := by
  cases parsed : readPrefix limits bytes with
  | error e => simp [readExact, parsed, bind, Except.bind]
  | ok value =>
    obtain ⟨found, next⟩ := value
    by_cases exactSize : next = bytes.length <;>
      simp [readExact, parsed, exactSize, bind, Except.bind, pure, Except.pure]

public theorem readPrefix_stop {limits : Limits} {bytes : Bytes} {locations : List Location}
    {next : Nat} (h : readPrefix limits bytes = .ok (locations, next)) :
    ∃ stop, next = stop + 1 ∧ bytes.data[stop]? = some 0 := by
  let compact := { limits.compact with maxCollectionSize := min limits.compact.maxCollectionSize limits.maxLocations }
  let reader : ThriftCompact.Traversal.Reader := ⟨bytes, compact, limits.varintMode⟩
  by_cases cap : bytes.length > limits.maxIndexBytes
  · simp [readPrefix, cap, throw] at h
  simp only [readPrefix, ite_eq_right cap] at h
  change ((ThriftCompact.Traversal.readStruct reader 0).mapError Error.compact >>= _) = _ at h
  cases parsed : ThriftCompact.Traversal.readStruct reader 0 with
  | error e => simp [parsed, Except.mapError, bind, Except.bind] at h
  | ok pair =>
    obtain ⟨fields, endOffset⟩ := pair
    simp only [parsed, Except.mapError, bind, Except.bind] at h
    split at h
    · cases h
    cases field : requireField fields 1 .list with
    | error e => simp [field] at h
    | ok f =>
      simp only [field] at h
      cases items : ThriftCompact.Traversal.readList reader Error.compact .struct
          (readLocation reader) f.start with
      | error e => rw [items] at h; cases h
      | ok pair =>
        obtain ⟨found, stop⟩ := pair
        rw [items] at h
        change (if stop ≠ f.stop then Except.error (Error.fieldExtent 1) else Except.ok (found, endOffset)) =
          Except.ok (locations, next) at h
        split at h
        · cases h
        · simp at h
          rw [← h.2]
          exact ThriftCompact.Traversal.readStruct_stop parsed

private theorem select_sound {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat}
    {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    (h : select limits snapshot g c = .ok (group, column)) :
    Selection limits snapshot g c group column := by
  unfold select at h
  split at h
  · rename_i chosen groupAt
    split at h
    · rename_i chosenColumn columnAt
      split at h
      · rename_i root leaves schema
        split at h
        · rename_i leaf leafAt
          dsimp only at h
          split at h
          · cases h
          rename_i profile
          split at h
          · cases h
          rename_i dataChunk
          split at h
          · cases h
          rename_i count
          split at h
          · cases h
          rename_i rowCap
          simp [pure, Except.pure] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨fanout, physical, width, arity, layout, columnType, path⟩ := not_not.mp profile
          have counts := not_not.mp count
          exact ⟨groupAt, columnAt,
            ⟨root, leaves, leaf, schema, fanout, leafAt, physical, width, arity, layout, columnType, path⟩,
            not_not.mp dataChunk, counts.2, counts.1, Nat.le_of_not_gt rowCap⟩
        · cases h
      · cases h
    · cases h
  · cases h

private theorem pageRows_sound {index : Nat} {kind : Page.Kind} {rows : Nat}
    (h : pageRows index kind = .ok rows) : FlatRows kind rows := by
  cases kind with
  | dataV1 info =>
    simp [pageRows] at h
    subst rows
    exact .v1 info
  | dataV2 info =>
    by_cases flat : info.numValues = info.numRows ∧ info.repetitionBytes = 0
    · simp [pageRows, flat] at h
      subst rows
      exact .v2 info flat.1 flat.2
    · simp [pageRows, flat] at h
  | dictionary info => simp [pageRows] at h
  | skipped info => simp [pageRows] at h

public theorem matchPages_sound {groupRows : Nat} {locations : List Location} {frames : List Page.Frame}
    {entries : List Entry} (h : matchPages groupRows locations frames = .ok entries) :
    entries.map Entry.location = locations ∧ entries.map Entry.frame = frames ∧
      Partition 0 groupRows entries := by
  suffices go : ∀ index start rev locs actual result,
      matchPages.go groupRows index start rev locs actual = .ok result →
      ∃ entries, result = rev.reverse ++ entries ∧
        entries.map Entry.location = locs ∧ entries.map Entry.frame = actual ∧
        Partition start groupRows entries by
    obtain ⟨suffix, rfl, locationOrder, frameOrder, rows⟩ := go 0 0 [] locations frames entries h
    simpa using And.intro locationOrder (And.intro frameOrder rows)
  intro index start rev locs
  induction locs generalizing index start rev with
  | nil =>
    intro actual result parsed
    cases actual with
    | nil =>
      by_cases last : start = groupRows
      · simp [matchPages.go, last] at parsed
        subst result
        subst groupRows
        exact ⟨[], by simp, rfl, rfl, .nil _⟩
      · simp [matchPages.go, last] at parsed
    | cons frame frames => simp [matchPages.go] at parsed
  | cons location locations ih =>
    intro actual result parsed
    cases actual with
    | nil => simp [matchPages.go] at parsed
    | cons frame frames =>
      simp only [matchPages.go] at parsed
      split at parsed
      · cases parsed
      rename_i offset
      split at parsed
      · cases parsed
      rename_i size
      split at parsed
      · cases parsed
      rename_i first
      cases counted : pageRows index frame.value.kind with
      | error e => simp [counted, bind, Except.bind] at parsed
      | ok rows =>
        simp only [counted, bind, Except.bind] at parsed
        split at parsed
        · cases parsed
        rename_i positive
        split at parsed
        · cases parsed
        let entry : Entry := ⟨location, frame, rows⟩
        obtain ⟨rest, resultEq, locations_eq, frames_eq, restRows⟩ :=
          ih (index + 1) (start + rows) (entry :: rev) frames result parsed
        refine ⟨entry :: rest, ?_, by simp [entry, locations_eq], by simp [entry, frames_eq],
          .cons (not_not.mp first) (Nat.pos_of_ne_zero positive) (pageRows_sound counted)
            (not_not.mp offset) (not_not.mp size) ?_⟩
        · simpa using resultEq
        · simpa [entry, Entry.rowStop, not_not.mp first] using restRows

private theorem validateAt_sound {limits : Limits} {snapshot : Snapshot.Checked}
    {group : Footer.RowGroup} {column : Footer.ColumnChunk} {offset size : Int} {result : Index}
    (h : validateAt limits snapshot group column offset size = .ok result) :
    ∃ (chunk : Footer.Span) (bytes : Bytes),
      Footer.checkDataSpan snapshot.footer.start offset size = some result.span ∧
      chunk.stop ≤ result.span.start ∧ bytes.length ≤ limits.maxIndexBytes ∧
      chunk.stop - chunk.start ≤ limits.maxChunkBytes ∧
      snapshot.bytes.slice? result.span.start (some result.span.stop) = some bytes ∧
      readPrefix limits bytes = .ok (result.pages.map Entry.location, bytes.length) ∧
      Page.columnSpan snapshot.footer.start column.metadata = some chunk ∧
      Page.readChunk limits.page snapshot.bytes chunk = .ok (result.pages.map Entry.frame) ∧
      Partition 0 group.numRows.toNat result.pages := by
  unfold validateAt at h
  split at h
  · cases h
  rename_i byteCap
  split at h
  · rename_i span spanEq
    split at h
    · rename_i chunk chunkEq
      split at h
      · cases h
      rename_i separated
      split at h
      · cases h
      rename_i chunkCap
      split at h
      · cases h
      rename_i bounded
      let bytes := Footer.fileBytes snapshot.bytes span.start span.stop
      change (do
        let locations ← readExact limits bytes
        let frames ← (Page.readChunk limits.page snapshot.bytes chunk).mapError Error.page
        pure (⟨span, ← matchPages group.numRows.toNat locations frames⟩ : Index)) = .ok result at h
      cases exactRead : readExact limits bytes with
      | error e => rw [exactRead] at h; cases h
      | ok locations =>
        rw [exactRead] at h
        cases framed : Page.readChunk limits.page snapshot.bytes chunk with
        | error e => simp only [framed, Except.mapError, bind, Except.bind] at h; cases h
        | ok frames =>
          simp only [framed, Except.mapError, bind, Except.bind] at h
          cases matched : matchPages group.numRows.toNat locations frames with
          | error e => rw [matched] at h; cases h
          | ok entries =>
            rw [matched] at h
            simp [pure, Except.pure] at h
            subst result
            obtain ⟨locationOrder, frameOrder, partition⟩ := matchPages_sound matched
            have advertised := Footer.checkDataSpan_some_iff.mp spanEq
            have sliceEq : snapshot.bytes.slice? span.start (some span.stop) = some bytes := by
              apply Bytes.slice?_eq_some_iff.mpr
              refine ⟨by simpa using Nat.le_of_lt advertised.2.2.2.1, by simpa using Nat.le_of_not_gt bounded,
                Bytes.ext ?_⟩
              rw [Bytes.toList_ofList]
              simp [bytes, Footer.fileBytes, Bytes.toList, ByteArray.data_extract]
            have length := Bytes.length_of_slice? sliceEq
            simp only [Option.getD_some] at length
            have cap : bytes.length ≤ limits.maxIndexBytes := by
              have start := advertised.1
              have stop := advertised.2.1
              omega
            exact ⟨chunk, bytes, spanEq, Nat.le_of_not_gt separated, cap,
              Nat.le_of_not_gt chunkCap, sliceEq, by rw [locationOrder]; exact readExact_ok_iff.mp exactRead,
              chunkEq, by simpa [frameOrder] using framed, partition⟩
    · cases h
  · cases h

public theorem validate_present {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat} {result : Index}
    (h : validate limits snapshot g c = .ok (some result)) :
    ∃ group column chunk bytes, Evidence limits snapshot g c result group column chunk bytes := by
  cases chosen : select limits snapshot g c with
  | error e => simp [validate, chosen, bind, Except.bind] at h
  | ok pair =>
    obtain ⟨group, column⟩ := pair
    have selected := select_sound chosen
    cases offset : column.offsetIndexOffset with
    | none =>
      cases size : column.offsetIndexLength <;>
        simp [validate, chosen, offset, size, bind, Except.bind, pure, Except.pure] at h
    | some start =>
      cases size : column.offsetIndexLength with
      | none => simp [validate, chosen, offset, size, bind, Except.bind] at h
      | some width =>
        cases read : validateAt limits snapshot group column start width with
        | error e => simp [validate, chosen, offset, size, read, bind, Except.bind, Functor.map, Except.map] at h
        | ok index =>
          simp [validate, chosen, offset, size, read, bind, Except.bind, Functor.map, Except.map] at h
          subst index
          obtain ⟨chunk, bytes, reference, separate, byteCap, chunkCap, sliced, parsed, span, frames, rows⟩ :=
            validateAt_sound read
          obtain ⟨startEq, stopEq, lower, nonempty, upper⟩ := Footer.checkDataSpan_some_iff.mp reference
          have widthEq : (↑(result.span.stop - result.span.start) : Int) = width := by omega
          exact ⟨group, column, chunk, bytes, selected, by simp [offset, startEq], size.trans (congrArg some widthEq.symm),
            ⟨lower, nonempty, upper⟩, separate, ⟨byteCap, chunkCap⟩, sliced, parsed, span, frames, rows⟩

public theorem validate_absent_iff {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat} :
    validate limits snapshot g c = .ok none ↔ ∃ group column,
      select limits snapshot g c = .ok (group, column) ∧
      column.offsetIndexOffset = none ∧ column.offsetIndexLength = none := by
  cases chosen : select limits snapshot g c with
  | error e => simp [validate, chosen, bind, Except.bind]
  | ok pair =>
    obtain ⟨group, column⟩ := pair
    cases offset : column.offsetIndexOffset <;> cases size : column.offsetIndexLength <;>
      simp [validate, chosen, offset, size, bind, Except.bind, pure, Except.pure]

public theorem readFile_ok_iff {limits : Limits} {source : Bytes} {group column : Nat}
    {result : Option Index} :
    readFile limits source group column = .ok result ↔ source.length ≤ limits.maxFileBytes ∧
      ∃ snapshot, Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
        validate limits snapshot group column = .ok result := by
  by_cases size : source.length ≤ limits.maxFileBytes
  · cases checked : Snapshot.check (Failure := Unit) limits.snapshot source <;>
      simp [readFile, Nat.not_lt_of_ge size, size, checked, Except.mapError, bind, Except.bind]
  · simp [readFile, Nat.lt_of_not_ge size, size, throw]

private theorem partition_location {start stop : Nat} {pages : List Entry}
    (h : Partition start stop pages) {entry : Entry} (member : entry ∈ pages) :
    entry.location.offset = entry.frame.header.start ∧
    entry.location.compressedSize = entry.frame.payload.stop - entry.frame.header.start := by
  induction h with
  | nil => simp at member
  | cons _ _ _ offset size _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨offset, size⟩
    · exact ih tail

public theorem evidence_pageGeometry {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat}
    {result : Index} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    {chunk : Footer.Span} {bytes : Bytes}
    (h : Evidence limits snapshot g c result group column chunk bytes)
    {entry : Entry} (member : entry ∈ result.pages) :
    entry.location.offset = entry.frame.header.start ∧
      entry.location.compressedSize =
        (entry.frame.header.stop - entry.frame.header.start) + entry.frame.value.compressedSize := by
  obtain ⟨offset, size⟩ := partition_location h.rows member
  have frameMember : entry.frame ∈ result.pages.map Entry.frame :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  have within := Page.readChunk_payloads_bounded h.frames entry.frame frameMember
  refine ⟨offset, ?_⟩
  have progress := within.headerProgress
  have adjacent := within.adjacent
  have width := within.payloadWidth
  omega

private theorem Partition.start_le {start stop : Nat} {pages : List Entry}
    (h : Partition start stop pages) : start ≤ stop := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons first positive _ _ _ _ ih =>
    simp only [Entry.rowStop, first] at ih
    omega

private theorem Partition.first_le_of_mem {start stop : Nat} {pages : List Entry}
    (h : Partition start stop pages) {entry : Entry} (member : entry ∈ pages) :
    start ≤ entry.location.firstRow := by
  induction h with
  | nil => simp at member
  | @cons start stop head rest first positive _ _ _ _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact Nat.le_of_eq first.symm
    · have later := ih tail
      simp only [Entry.rowStop, first] at later
      omega

public theorem partition_ordered {start stop : Nat} {pages : List Entry}
    (h : Partition start stop pages) :
    pages.Pairwise (fun first second =>
      first.rowStop ≤ second.location.firstRow ∧ first.location.firstRow < second.location.firstRow) := by
  induction h with
  | nil => exact .nil
  | @cons start stop entry rest first positive rows offset size next ih =>
    refine .cons (fun later member => ⟨Partition.first_le_of_mem next member, ?_⟩) ih
    have bound := Partition.first_le_of_mem next member
    simp only [Entry.rowStop] at bound
    omega

public theorem partition_rowMultiplicity {start stop : Nat} {pages : List Entry}
    (h : Partition start stop pages) (row : Nat) :
    pages.countP (fun entry => decide (entry.location.firstRow ≤ row ∧ row < entry.rowStop)) =
      if start ≤ row ∧ row < stop then 1 else 0 := by
  induction h with
  | nil => simp
  | @cons start stop entry rest first positive rows offset size next ih =>
    have bound := Partition.start_le next
    have progress : start < entry.rowStop := by simp [Entry.rowStop, first, positive]
    rw [List.countP_cons, ih]
    by_cases firstRange : start ≤ row ∧ row < entry.rowStop
    · have inRange : start ≤ row ∧ row < stop := by omega
      simp [first, firstRange, inRange]
    · have equivalent : (entry.rowStop ≤ row ∧ row < stop) ↔ (start ≤ row ∧ row < stop) := by omega
      simp [first, firstRange, equivalent]

end Silmaril.Proofs.Formats.Parquet.OffsetIndex
