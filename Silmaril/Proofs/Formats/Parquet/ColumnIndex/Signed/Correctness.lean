module

public import Silmaril.Formats.Parquet.ColumnIndex.Signed.Defs
import all Silmaril.Formats.Parquet.ColumnIndex.Signed.Defs
import Silmaril.Formats.Parquet.ColumnIndex.Thms
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.ColumnIndex.Signed

open Silmaril.Formats.Parquet
open Silmaril.Formats.ThriftCompact
open Silmaril.Formats.Parquet.ColumnIndex (BoundaryOrder Claim Index)
open Silmaril.Formats.Parquet.ColumnIndex.Signed

public theorem checkOrder_sound {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩}
    (h : checkOrder limits snapshot binding = .ok ()) : SignedOrder limits snapshot binding := by
  cases selected : readOrderFields limits snapshot binding with
  | error reason => simp [checkOrder, selected, bind, Except.bind] at h
  | ok fields =>
    simp only [checkOrder, selected, bind, Except.bind] at h
    split at h
    · cases h
    rename_i annotation
    have unannotated : ∀ field ∈ fields.leaf, field.id ≠ 6 ∧ field.id ≠ 10 := by
      intro field member
      constructor <;> intro equal <;>
        exact annotation (List.any_eq_true.mpr ⟨field, member, by simp [equal]⟩)
    split at h
    · rename_i member singleton
      split at h
      · cases h
      rename_i typeOrder
      split at h
      · cases h
      rename_i structType
      cases payload : Traversal.readStruct fields.reader member.start with
      | error reason => simp [readStruct, payload, Except.mapError] at h
      | ok result =>
        obtain ⟨members, next⟩ := result
        simp [readStruct, payload, Except.mapError, throw, pure, Except.pure] at h
        refine ⟨fields, member, selected, unannotated, singleton, not_not.mp typeOrder,
          not_not.mp structType, ?_⟩
        simpa [h.1, h.2] using payload
    · cases h

private theorem readBound_sound {source : Silmaril.Formats.Bytes} {value : Int32}
    (h : readBound source = .ok value) : Plain.decodeInt32 1 source = .ok [value] := by
  unfold readBound at h
  split at h
  · cases h; assumption
  · cases h

private theorem checkBounds_sound {claim : Claim} {slots : Slots} {bounds : Bounds}
    (h : checkBounds claim slots = .ok bounds) :
    Plain.decodeInt32 1 claim.lower = .ok [bounds.lower] ∧
    Plain.decodeInt32 1 claim.upper = .ok [bounds.upper] ∧
    ∀ value, some value ∈ slots → bounds.contains value := by
  cases lo : readBound claim.lower with
  | error => simp [checkBounds, lo, bind, Except.bind] at h
  | ok lower =>
    cases hi : readBound claim.upper with
    | error => simp [checkBounds, lo, hi, bind, Except.bind] at h
    | ok upper =>
      simp only [checkBounds, lo, hi, bind, Except.bind] at h
      split at h
      · rename_i within
        cases h
        refine ⟨readBound_sound lo, readBound_sound hi, fun value member => ?_⟩
        exact of_decide_eq_true (List.all_eq_true.mp within value
          (List.mem_filterMap.mpr ⟨some value, member, rfl⟩))
      · cases h

public theorem checkPage_sound {claim : Claim} {count : Option Int} {slots : Slots}
    {bounds : Option Bounds} (h : checkPage claim count slots = .ok bounds) :
    PageValid claim count slots bounds := by
  unfold checkPage at h
  dsimp only at h
  split at h
  · cases h
  rename_i flags
  have nullFlag : claim.allNull = true ↔ ∀ slot ∈ slots, slot = none := by
    rw [not_not.mp flags]
    simp
  cases counted : checkNullCount count (slots.countP Option.isNone) with
  | error => simp [counted, bind, Except.bind] at h
  | ok checked =>
    have countCheck : ∀ n, count = some n → n = (slots.countP Option.isNone : Int) := by
      intro n eq
      simpa [checkNullCount, eq] using counted
    simp only [counted, bind, Except.bind] at h
    refine ⟨nullFlag, countCheck, ?_⟩
    split at h
    · cases h
      assumption
    · rename_i present
      cases checkedBounds : checkBounds claim slots with
      | error => simp [checkedBounds, Functor.map, Except.map] at h
      | ok result =>
        simp [checkedBounds, Functor.map, Except.map] at h
        subst bounds
        exact ⟨Bool.eq_false_iff.mpr present, checkBounds_sound checkedBounds⟩

public theorem checkEach_sound {count : Nat → Option Int} {ordinal : Nat} {claims : List Claim}
    {pages : List Slots} {bounds : List (Option Bounds)}
    (h : checkEach count ordinal claims pages = .ok bounds) :
    PagesValid count ordinal claims pages bounds := by
  have same : claims.length = pages.length := by
    by_contra different
    simp [checkEach, different] at h
  simp only [checkEach, same, ne_self_iff_false, ite_false] at h
  induction claims generalizing ordinal pages bounds with
  | nil =>
    cases pages with
    | nil => cases h; exact .nil ordinal
    | cons => simp at same
  | cons claim claims ih =>
    cases pages with
    | nil => simp at same
    | cons slots pages =>
      simp only [List.length_cons, Nat.succ.injEq] at same
      simp only [List.zip_cons_cons, List.zipIdx_cons, List.mapM_cons] at h
      cases one : checkPage claim (count ordinal) slots with
      | error reason => simp [one, Except.mapError, bind, Except.bind] at h
      | ok bound =>
        have first : (checkPage claim (count ordinal) slots).mapError
            (ColumnIndex.Signed.Error.page ordinal) = .ok bound := by
          simp [one, Except.mapError]
        rw [first] at h
        simp only [bind, Except.bind] at h
        cases rest : ((claims.zip pages).zipIdx (ordinal + 1)).mapM
            (fun entry => (checkPage entry.1.1 (count entry.2) entry.1.2).mapError
              (ColumnIndex.Signed.Error.page entry.2)) with
        | error reason => rw [rest] at h; cases h
        | ok tail =>
          rw [rest] at h
          simp [pure, Except.pure] at h
          subst bounds
          exact .cons (checkPage_sound one) (ih same rest)

private theorem nondecreasing_iff (values : List Int) :
    nondecreasing values = true ↔ values.Pairwise (· ≤ ·) := by
  induction values with
  | nil => simp [nondecreasing]
  | cons a tail ih =>
    cases tail with
    | nil => simp [nondecreasing]
    | cons b rest =>
      rw [nondecreasing, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨ab, pairs⟩
        refine List.pairwise_cons.mpr ⟨?_, pairs⟩
        intro value member
        rcases List.mem_cons.mp member with equal | later
        · simpa [equal] using ab
        · exact Int.le_trans ab ((List.pairwise_cons.mp pairs).1 value later)
      · intro pairs
        exact ⟨(List.pairwise_cons.mp pairs).1 b (by simp), (List.pairwise_cons.mp pairs).2⟩

public theorem ordered_iff {order : BoundaryOrder} {values : List Int} :
    ordered order values = true ↔ Ordered order values := by
  cases order with
  | unordered => simp [ordered, Ordered]
  | ascending => exact nondecreasing_iff values
  | descending =>
    rw [ordered, nondecreasing_iff, List.pairwise_map, Ordered]
    exact ⟨List.Pairwise.imp (by intro a b h; change -a ≤ -b at h; omega),
      List.Pairwise.imp (by intro a b h; omega)⟩

public theorem declaredCount_eq (index : Index) (page : Nat) :
    declaredCount index page = index.raw.nullCounts.bind (·[page]?) := by
  cases present : index.raw.nullCounts <;> simp [declaredCount, present]

public theorem check_sound {index : Index} {pages : List Slots} {bounds : List (Option Bounds)}
    (h : check index pages = .ok bounds) : Verified index pages bounds := by
  cases checked : checkEach (declaredCount index) 0 index.raw.claims pages with
  | error reason => simp [check, checked, bind, Except.bind] at h
  | ok computed =>
    by_cases lower : ordered index.raw.order (endpoint Bounds.lower computed) = true <;>
      by_cases upper : ordered index.raw.order (endpoint Bounds.upper computed) = true <;>
      simp [check, checked, lower, upper, bind, Except.bind, throw, pure, Except.pure] at h
    subst bounds
    exact ⟨checkEach_sound checked, ordered_iff.mp lower, ordered_iff.mp upper⟩

private theorem FlatRows.slots_eq {header : Page.Header} {count : Nat}
    (h : OffsetIndex.FlatRows header.kind count) : FlatColumn.pageSlots header = count := by
  cases header
  cases h with
  | v1 => simp [FlatColumn.pageSlots]
  | v2 _ counts _ => simpa [FlatColumn.pageSlots] using counts

public theorem splitPages_eq {decode : FlatColumn.DecodePage Int32 FlatScan.AdapterError}
    {leaf : Footer.SchemaElement} {metadata : Footer.ColumnMetadata} {source : Silmaril.Formats.Bytes}
    {start stop : Nat} {entries : List OffsetIndex.Entry} {pages : List Slots}
    (partition : OffsetIndex.Partition start stop entries)
    (original : List.Forall₂ (FlatColumn.CallbackWire decode leaf metadata source)
      (entries.map OffsetIndex.Entry.frame) pages) :
    splitPages entries pages.flatten = pages := by
  unfold splitPages
  suffices walk : ∀ (reversePrefix : List Slots),
      ((entries.foldl (fun (remaining, reversed) entry =>
        (remaining.drop entry.rowCount, remaining.take entry.rowCount :: reversed))
          (pages.flatten, reversePrefix)).2.reverse) = reversePrefix.reverse ++ pages by
    simpa using walk []
  intro prefixRows
  induction partition generalizing pages prefixRows with
  | nil => cases original; simp
  | @cons start stop entry rest first positive rows offset size next ih =>
    cases original with
    | cons head tail =>
      have count := head.2.trans (FlatRows.slots_eq rows)
      simp only [List.foldl_cons, List.flatten_cons, ← count, List.take_append_length,
        List.drop_append_length]
      rw [ih tail, List.reverse_cons, List.append_assoc]
      rfl

public theorem read_error_iff {limits : Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩} {group : Nat}
    {reason : FlatColumn.Error FlatScan.AdapterError} :
    ColumnIndex.Signed.read limits binding group = .error reason ↔ readFull limits binding group = .error reason := by
  cases full : readFull limits binding group <;> simp [ColumnIndex.Signed.read, full, Except.map]

public theorem read_ok_iff {limits : Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩} {group : Nat}
    {result : Result} :
    ColumnIndex.Signed.read limits binding group = .ok result ↔
      readFull limits binding group = .ok result.rows ∧
      result.index = diagnose limits binding group result.rows := by
  cases result
  cases full : readFull limits binding group <;> simp [ColumnIndex.Signed.read, full, Except.map, eq_comm]
  intro same
  cases same
  rfl

private theorem diagnose_present {limits : Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩} {group : Nat}
    {slots : Slots} {bounds : List (Option Bounds)}
    (h : diagnose limits binding group slots = .ok (some bounds)) :
    ∃ index, ColumnIndex.validate limits.indexFraming snapshot group binding.columnOrdinal = .ok (some index) ∧
      checkOrder limits.index.offsetIndex.snapshot.footer snapshot binding = .ok () ∧
      check index (splitPages index.offsetIndex.pages slots) = .ok bounds := by
  cases indexed : ColumnIndex.validate limits.indexFraming snapshot group binding.columnOrdinal with
  | error reason => simp [diagnose, indexed, Except.mapError, bind, Except.bind] at h
  | ok optional =>
    cases optional with
    | none => simp [diagnose, indexed, Except.mapError, bind, Except.bind, pure, Except.pure] at h
    | some index =>
      cases supported : checkOrder limits.index.offsetIndex.snapshot.footer snapshot binding with
      | error reason => simp [diagnose, indexed, supported, Except.mapError, bind, Except.bind] at h
      | ok done =>
        cases done
        cases checked : check index (splitPages index.offsetIndex.pages slots) with
        | error reason =>
          simp [diagnose, indexed, supported, checked, Except.mapError, bind, Except.bind, Functor.map, Except.map] at h
        | ok computed =>
          simp [diagnose, indexed, supported, checked, Except.mapError, bind, Except.bind, Functor.map, Except.map] at h
          subst bounds
          exact ⟨index, rfl, rfl, checked⟩

/-- Verification concerns exactly the original decoded pages, in checked
OffsetIndex frame order, and the original claims from the same snapshot. -/
public theorem read_verified {limits : Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩} {group : Nat}
    {result : Result} {bounds : List (Option Bounds)}
    (readOk : read limits binding group = .ok result) (verified : result.index = .ok (some bounds)) :
    ∃ index selected column chunk offsetBytes bytes pages,
      ColumnIndex.Evidence limits.indexFraming snapshot group binding.columnOrdinal
        index selected column chunk offsetBytes bytes ∧
      SignedOrder limits.index.offsetIndex.snapshot.footer snapshot binding ∧
      List.Forall₂ (FlatColumn.CallbackWire (decodePage limits.scalar layout) binding.leaf
        column.metadata snapshot.bytes) (index.offsetIndex.pages.map OffsetIndex.Entry.frame) pages ∧
      result.rows = pages.flatten ∧ Verified index pages bounds := by
  obtain ⟨full, diagnostic⟩ := read_ok_iff.mp readOk
  obtain ⟨index, indexed, order, checked⟩ := diagnose_present (diagnostic.symm.trans verified)
  obtain ⟨selected, indexColumn, indexChunk, offsetBytes, bytes, evidence⟩ :=
    ColumnIndex.validate_present indexed
  unfold readFull at full
  obtain ⟨readGroup, column, chunk, frames, pages, groupAt, columnAt, _, _, _, _, span, framed, _,
    decoded, flattened, _⟩ := FlatColumn.readColumn_wire full
  have groupEq := Option.some.inj (groupAt.symm.trans evidence.offsets.selected.groupAt)
  subst readGroup
  have columnEq := Option.some.inj (columnAt.symm.trans evidence.offsets.selected.columnAt)
  subst column
  have chunkEq := Option.some.inj (span.symm.trans evidence.offsets.columnSpan)
  subst chunk
  have sameFrames := Except.ok.inj (framed.symm.trans evidence.offsets.frames)
  subst frames
  rw [flattened, splitPages_eq evidence.offsets.rows decoded] at checked
  exact ⟨index, selected, indexColumn, indexChunk, offsetBytes, bytes, pages, evidence, checkOrder_sound order,
    decoded, flattened, check_sound checked⟩

end Silmaril.Proofs.Formats.Parquet.ColumnIndex.Signed
