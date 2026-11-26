module

public import Silmaril.Formats.Relational.BinaryObservation.Defs
import Silmaril.Formats.Parquet.ScalarPage.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.BinaryObservation

open Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Relational.BinaryObservation
open Arrow.BinaryView Parquet

theorem observation_eq_iff {left right : Field} {leftSlots rightSlots : List Slot} :
    observation left leftSlots = observation right rightSlots ↔
      left = right ∧ leftSlots = rightSlots := by
  constructor
  · intro equal
    have labels := congrArg (fun result : Observation => List.ofFn result.schema.kind) equal
    have fields : (left.name, left.nullable) = (right.name, right.nullable) := by
      simpa [observation, Field.schema, List.ofFn_succ] using labels
    have fieldEq : left = right := by cases left; cases right; simpa using fields
    have slots := congrArg (fun result : Observation =>
      result.rows.flatMap fun row => List.ofFn fun index : Fin result.schema.width => (row index : Slot)) equal
    exact ⟨fieldEq, by simpa [observation, Field.schema, List.ofFn_succ, List.flatMap_map] using slots⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem observation_rowCount (field : Field) (chunks : List (List Slot)) :
    (observation field chunks.flatten).rowCount = (chunks.map List.length).sum := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
    simp [Scan.Observation.rowCount, observation] at ih ⊢
    rw [ih]

theorem checkColumn_ok_iff {expected : Field} {column : ParquetColumn} :
    checkColumn expected column = .ok () ↔ column.field = expected ∧
      column.physicalType = .byteArray ∧ column.codec = 0 ∧ column.levels = expected.levels := by
  unfold checkColumn
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem observeIpc_ok_iff {expected : Field} {ipc : Arrow.Limits} {limits : Column.Limits}
    {input : KBytes} {result : Observation} :
    observeIpc expected ipc limits input = .ok result ↔
      ∃ batches : List (List (Option KBytes)),
        Stream.read ipc limits input = .ok ⟨⟨expected.name, expected.nullable, .binary⟩, batches⟩ ∧
        result = observation expected (ipcSlots batches) := by
  cases read : Stream.read ipc limits input with
  | error cause => simp [observeIpc, read]
  | ok stream =>
    rcases stream with ⟨⟨name, nullable, kind⟩, batches⟩
    cases kind with
    | utf8 =>
      simp [observeIpc, read]
      intro _ equal
      have kind := congrArg (fun result : Stream.Observed => result.field.kind) equal
      cases kind
    | binary =>
      by_cases equal : (⟨name, nullable⟩ : Field) = expected
      · subst expected
        simp [observeIpc, read, eq_comm]
        constructor
        · intro observed
          exact ⟨batches, rfl, observed⟩
        · rintro ⟨other, same, observed⟩
          cases same
          exact observed
      · constructor
        · intro ok
          simp [observeIpc, read, equal] at ok
        · rintro ⟨other, same, _⟩
          have fieldEq := congrArg Stream.Observed.field (Except.ok.inj same)
          cases expected
          cases fieldEq
          exact (equal rfl).elim

theorem readPage_ok_iff {field : Field} {limits : PageLimits} {window : PageWindow}
    {slots : List Slot} :
    readPage field limits window = .ok slots ↔
      ∃ data raw,
        window.header.kind = .dataV2 data ∧ window.header.crc = none ∧
        ScalarPage.decode (.byteArray limits.values) (pageParameters field window.header data)
          limits.scalar window.body = .ok raw ∧
        slots = raw.map (Option.map Bytes.toList) := by
  cases kind : window.header.kind with
  | dataV1 _ | dictionary _ | skipped _ => simp [readPage, kind]
  | dataV2 data =>
    cases crc : window.header.crc with
    | some _ => simp [readPage, kind, crc]
    | none =>
      cases read : ScalarPage.decode (.byteArray limits.values)
          (pageParameters field window.header data) limits.scalar window.body with
      | error cause => simp [readPage, kind, crc, read, Except.mapError]
      | ok raw => simp [readPage, kind, crc, read, Except.mapError, eq_comm]

theorem readPage_count {field : Field} {limits : PageLimits} {window : PageWindow}
    {slots : List Slot} {data : Page.DataV2} (header : window.header.kind = .dataV2 data)
    (read : readPage field limits window = .ok slots) : slots.length = data.numValues := by
  obtain ⟨actual, raw, kind, _, decoded, rfl⟩ := readPage_ok_iff.mp read
  rw [header] at kind
  cases kind
  simpa [pageParameters] using (ScalarPage.decode_counts decoded).1

private theorem readPages_toOption (field : Field) (limits : PageLimits)
    (windows : List PageWindow) (index : Nat) :
    (readPages field limits index windows).toOption =
      (windows.mapM (readPage field limits)).toOption := by
  induction windows generalizing index with
  | nil => rfl
  | cons window rest ih =>
    cases page : readPage field limits window with
    | error cause => simp [readPages, page, List.mapM_cons, Except.mapError]; rfl
    | ok slots =>
      have tail := ih (index + 1)
      cases full : readPages field limits (index + 1) rest <;>
        cases plain : rest.mapM (readPage field limits) <;>
        simp [full, plain, Except.toOption] at tail
      all_goals simp [readPages, page, List.mapM_cons, Except.mapError, full, plain,
        Bind.bind, Except.bind, pure, Except.pure, tail, Except.toOption]

theorem observeParquet_ok_iff {expected : Field} {limits : PageLimits} {column : ParquetColumn}
    {windows : List PageWindow} {result : Observation} :
    observeParquet expected limits column windows = .ok result ↔
      checkColumn expected column = .ok () ∧ ∃ pages,
        windows.mapM (readPage expected limits) = .ok pages ∧
        result = observation expected pages.flatten := by
  cases binding : checkColumn expected column with
  | error cause => simp [observeParquet, binding, Bind.bind, Except.bind]
  | ok checked =>
    cases checked
    have decoded := readPages_toOption expected limits windows 0
    cases read : readPages expected limits 0 windows <;>
      cases plain : windows.mapM (readPage expected limits) <;>
      simp [read, plain, Except.toOption] at decoded
    all_goals simp [observeParquet, binding, read, eq_comm, Bind.bind, Except.bind, pure, Except.pure, decoded]

private theorem readPages_first_error {field : Field} {limits : PageLimits}
    {before after : List PageWindow} {window : PageWindow} {cause : PageError}
    (earlier : ∀ prior ∈ before, ∃ slots, readPage field limits prior = .ok slots)
    (failure : readPage field limits window = .error cause) (start : Nat) :
    readPages field limits start (before ++ window :: after) =
      .error (.page (start + before.length) cause) := by
  induction before generalizing start with
  | nil => simp [readPages, failure, Except.mapError]; rfl
  | cons first rest ih =>
    obtain ⟨slots, firstRead⟩ := earlier first (by simp)
    have tail := ih (fun prior member => earlier prior (by simp [member])) (start + 1)
    simp [readPages, firstRead, tail, Except.mapError, Nat.add_comm, Nat.add_left_comm]
    rfl

theorem observeParquet_first_error {expected : Field} {limits : PageLimits} {column : ParquetColumn}
    {before after : List PageWindow} {window : PageWindow} {cause : PageError}
    (bound : checkColumn expected column = .ok ())
    (earlier : ∀ prior ∈ before, ∃ slots, readPage expected limits prior = .ok slots)
    (failure : readPage expected limits window = .error cause) :
    observeParquet expected limits column (before ++ window :: after) =
      .error (.page before.length cause) := by
  simp [observeParquet, bound, readPages_first_error earlier failure 0]; rfl

theorem common_observation_iff {parquetField ipcField : Field} {limits : PageLimits}
    {column : ParquetColumn} {windows : List PageWindow} {pages : List (List Slot)}
    {ipc : Arrow.Limits} {viewLimits : Column.Limits} {input : KBytes}
    {batches : List (List (Option KBytes))}
    (bound : checkColumn parquetField column = .ok ())
    (pageRead : windows.mapM (readPage parquetField limits) = .ok pages)
    (ipcRead : Stream.read ipc viewLimits input = .ok ⟨⟨ipcField.name, ipcField.nullable, .binary⟩, batches⟩) :
    (∃ common, observeParquet parquetField limits column windows = .ok common ∧
      observeIpc ipcField ipc viewLimits input = .ok common) ↔
      parquetField = ipcField ∧ pages.flatten = ipcSlots batches := by
  have parquet := observeParquet_ok_iff.mpr ⟨bound, pages, pageRead, rfl⟩
  have arrow := observeIpc_ok_iff.mpr ⟨batches, ipcRead, rfl⟩
  rw [parquet, arrow]
  constructor
  · rintro ⟨common, left, right⟩
    exact observation_eq_iff.mp ((Except.ok.inj left).trans (Except.ok.inj right).symm)
  · intro equal
    exact ⟨_, rfl, congrArg Except.ok (observation_eq_iff.mpr equal).symm⟩

end Silmaril.Proofs.Formats.Relational.BinaryObservation
