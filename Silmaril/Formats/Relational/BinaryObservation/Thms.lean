module

public import Silmaril.Formats.Relational.BinaryObservation.Defs
import Silmaril.Proofs.Formats.Relational.BinaryObservation.Correctness

/-! Exact admission, byte-row observations, and indexed errors. -/

public section

namespace Silmaril.Formats.Relational.BinaryObservation

open Silmaril.Relational
open Arrow.BinaryView Parquet

/-- A one-column observation is determined by the exact descriptor and the
ordered nullable octet slots. -/
theorem observation_eq_iff {left right : Field} {leftSlots rightSlots : List Slot} :
    observation left leftSlots = observation right rightSlots ↔
      left = right ∧ leftSlots = rightSlots :=
  Proofs.Formats.Relational.BinaryObservation.observation_eq_iff

/-- Each checked slot contributes one row. Empty pages or batches contribute
zero rows. -/
theorem observation_rowCount (field : Field) (chunks : List (List Slot)) :
    (observation field chunks.flatten).rowCount = (chunks.map List.length).sum :=
  Proofs.Formats.Relational.BinaryObservation.observation_rowCount field chunks

/-- The supplied column must match the declared descriptor and the flat
uncompressed BYTE_ARRAY profile. -/
theorem checkColumn_ok_iff {expected : Field} {column : ParquetColumn} :
    checkColumn expected column = .ok () ↔ column.field = expected ∧
      column.physicalType = .byteArray ∧ column.codec = 0 ∧ column.levels = expected.levels :=
  Proofs.Formats.Relational.BinaryObservation.checkColumn_ok_iff

/-- Success requires the matching BinaryView field and all batches through
the underlying reader's exact EOS. -/
theorem observeIpc_ok_iff {expected : Field} {ipc : Arrow.Limits} {limits : Column.Limits}
    {input : KBytes} {result : Observation} :
    observeIpc expected ipc limits input = .ok result ↔
      ∃ batches : List (List (Option KBytes)),
        Stream.read ipc limits input = .ok ⟨⟨expected.name, expected.nullable, .binary⟩, batches⟩ ∧
        result = observation expected (ipcSlots batches) :=
  Proofs.Formats.Relational.BinaryObservation.observeIpc_ok_iff

/-- Preserve the original IPC reader error, including its batch index. -/
theorem observeIpc_reader_error {expected : Field} {ipc : Arrow.Limits} {limits : Column.Limits}
    {input : KBytes} {cause : Stream.Error} (failure : Stream.read ipc limits input = .error cause) :
    observeIpc expected ipc limits input = .error (.reader cause) := by
  rw [observeIpc, failure]

/-- A successful window is V2 with no CRC and yields the existing scalar
decoder's exact PLAIN nullable slots projected to octets. -/
theorem readPage_ok_iff {field : Field} {limits : PageLimits} {window : PageWindow}
    {slots : List Slot} :
    readPage field limits window = .ok slots ↔
      ∃ data raw,
        window.header.kind = .dataV2 data ∧ window.header.crc = none ∧
        ScalarPage.decode (.byteArray limits.values) (pageParameters field window.header data)
          limits.scalar window.body = .ok raw ∧
        slots = raw.map (Option.map Bytes.toList) :=
  Proofs.Formats.Relational.BinaryObservation.readPage_ok_iff

/-- The checked V2 page yields exactly its advertised slot count. -/
theorem readPage_count {field : Field} {limits : PageLimits} {window : PageWindow}
    {slots : List Slot} {data : Page.DataV2} (header : window.header.kind = .dataV2 data)
    (read : readPage field limits window = .ok slots) : slots.length = data.numValues :=
  Proofs.Formats.Relational.BinaryObservation.readPage_count header read

/-- Success checks the declared column and every supplied window in order.
The result contains exactly the concatenated page slots. -/
theorem observeParquet_ok_iff {expected : Field} {limits : PageLimits} {column : ParquetColumn}
    {windows : List PageWindow} {result : Observation} :
    observeParquet expected limits column windows = .ok result ↔
      checkColumn expected column = .ok () ∧ ∃ pages,
        windows.mapM (readPage expected limits) = .ok pages ∧
        result = observation expected pages.flatten :=
  Proofs.Formats.Relational.BinaryObservation.observeParquet_ok_iff

/-- The first failed window returns its ordinal and original page cause.
No completed observation is returned. -/
theorem observeParquet_first_error {expected : Field} {limits : PageLimits} {column : ParquetColumn}
    {before after : List PageWindow} {window : PageWindow} {cause : PageError}
    (bound : checkColumn expected column = .ok ())
    (earlier : ∀ prior ∈ before, ∃ slots, readPage expected limits prior = .ok slots)
    (failure : readPage expected limits window = .error cause) :
    observeParquet expected limits column (before ++ window :: after) =
      .error (.page before.length cause) :=
  Proofs.Formats.Relational.BinaryObservation.observeParquet_first_error bound earlier failure

/-- Successfully decoded sources agree exactly when their descriptors and
ordered nullable octet rows agree. Page and batch boundaries are unobserved. -/
theorem common_observation_iff {parquetField ipcField : Field} {limits : PageLimits}
    {column : ParquetColumn} {windows : List PageWindow} {pages : List (List Slot)}
    {ipc : Arrow.Limits} {viewLimits : Column.Limits} {input : KBytes}
    {batches : List (List (Option KBytes))}
    (bound : checkColumn parquetField column = .ok ())
    (pageRead : windows.mapM (readPage parquetField limits) = .ok pages)
    (ipcRead : Stream.read ipc viewLimits input = .ok ⟨⟨ipcField.name, ipcField.nullable, .binary⟩, batches⟩) :
    (∃ common, observeParquet parquetField limits column windows = .ok common ∧
      observeIpc ipcField ipc viewLimits input = .ok common) ↔
      parquetField = ipcField ∧ pages.flatten = ipcSlots batches :=
  Proofs.Formats.Relational.BinaryObservation.common_observation_iff bound pageRead ipcRead

end Silmaril.Formats.Relational.BinaryObservation
