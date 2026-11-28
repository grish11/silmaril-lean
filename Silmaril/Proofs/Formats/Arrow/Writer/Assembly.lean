module

public import Silmaril.Formats.Arrow.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.Writer.Buffers
import Silmaril.Proofs.Formats.Arrow.Writer.Columns
import Silmaril.Formats.Arrow.Layout.Thms
import Silmaril.Prelude.Bytes.Equiv.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.Writer

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Writer

private structure BufferBytes (a b : KBytes) : Prop where
  left : a.wf = true
  right : b.wf = true
  bytes : a ≈ b

private theorem BufferBytes.length {a b : KBytes} (same : BufferBytes a b) :
    a.len = b.len :=
  KBytes.len_eq_of_equiv same.left same.right same.bytes

private theorem BufferBytes.validAt {a b : KBytes} (same : BufferBytes a b) (index : Nat) :
    Body.validAt a index = Body.validAt b index := by
  rw [Body.validAt, Body.validAt, same.length,
    KBytes.get?_congr same.left same.right same.bytes]

private theorem BufferBytes.offsetAt {a b : KBytes} (same : BufferBytes a b) (index : Nat) :
    Body.offsetAt a index = Body.offsetAt b index := by
  rw [Body.offsetAt, Body.offsetAt, KBytes.readLE_congr same.left same.right same.bytes]

private theorem BufferBytes.bitmapExtent {a b : KBytes} (same : BufferBytes a b) (rows : Nat) :
    Body.BitmapExtent a rows ↔ Body.BitmapExtent b rows := by
  rw [Body.BitmapExtent, Body.BitmapExtent, same.length]

private theorem cellsTransfer {a b : Body.ColumnBuffers} {indices : List Nat} {values : Column}
    (cell : ∀ index value, Body.CellWire b index value → Body.CellWire a index value)
    (wire : Body.CellsWire b indices values) : Body.CellsWire a indices values := by
  induction indices generalizing values with
  | nil => cases values <;> exact wire
  | cons index indices ih =>
    cases values with
    | nil => exact wire
    | cons value values => exact ⟨cell index value wire.1, ih wire.2⟩

private theorem int32Transfer {bm bm' words words' : KBytes} {node : FieldNode} {values : Column}
    (bitmap : BufferBytes bm bm') (data : BufferBytes words words')
    (wire : Body.ColumnWire node (.int32 bm' words') values) :
    Body.ColumnWire node (.int32 bm words) values := by
  rcases wire with ⟨bitmapFit, wordFit, cells, nulls⟩
  refine ⟨(bitmap.bitmapExtent _).mpr bitmapFit, ?_, cellsTransfer ?_ cells, nulls⟩
  · change 4 * node.length ≤ words.len
    rw [data.length]
    exact wordFit
  · intro index value h
    simpa only [Body.CellWire, Body.ColumnBuffers.validity, bitmap.validAt,
      KBytes.readLE_congr data.left data.right data.bytes] using h

private theorem utf8Transfer {bm bm' off off' data data' : KBytes}
    {node : FieldNode} {values : Column}
    (bitmap : BufferBytes bm bm') (offsets : BufferBytes off off')
    (bytes : BufferBytes data data')
    (wire : Body.ColumnWire node (.utf8 bm' off' data') values) :
    Body.ColumnWire node (.utf8 bm off data) values := by
  rcases wire with ⟨bitmapFit, offsetFit, cells, nulls⟩
  refine ⟨(bitmap.bitmapExtent _).mpr bitmapFit, ?_, cellsTransfer ?_ cells, nulls⟩
  · simpa only [Body.PayloadExtent, offsets.length, offsets.offsetAt, bytes.length] using offsetFit
  · intro index value h
    obtain ⟨valid, bit, lo, hi, atLo, atHi, order, fits, observed⟩ := h
    refine ⟨valid, (bitmap.validAt index).trans bit, lo, hi, (offsets.offsetAt index).trans atLo,
      (offsets.offsetAt (index + 1)).trans atHi, order, bytes.length ▸ fits, ?_⟩
    have bound : lo + (hi - lo) ≤ data.len := by rw [bytes.length]; omega
    have sameSlice : (data.slice lo (hi - lo)).toByteArray = (data'.slice lo (hi - lo)).toByteArray :=
      KBytes.toByteArray_eq_iff.mpr (KBytes.slice_congr bytes.left bytes.right bytes.bytes bound)
    simpa only [sameSlice] using observed

private theorem pullPiece {body : KBytes} {offset : Nat} {piece : KBytes} {pieces : List KBytes}
    {descriptors : List Buffer}
    (bodyWF : body.wf = true) (pieceWF : piece.wf = true)
    (bounds : ∀ b ∈ descriptors, b.offset + b.length ≤ body.len)
    (wire : PackedWire body.toList offset (piece :: pieces) descriptors) :
      ∃ tail, descriptors = ⟨offset, piece.len⟩ :: tail ∧
        BufferBytes (Body.sliceBuffer body ⟨offset, piece.len⟩) piece ∧
        PackedWire body.toList (offset + piece.len + padding piece.len) pieces tail := by
  cases descriptors with
  | nil => exact wire.elim
  | cons head tail =>
    obtain ⟨rfl, exactBytes, remaining⟩ := wire
    have fits : offset + piece.len ≤ body.len := bounds ⟨offset, piece.len⟩ (by simp)
    exact ⟨tail, rfl, ⟨KBytes.wf_slice _ _ _ bodyWF fits, pieceWF,
      (KBytes.toList_slice _ _ _ bodyWF fits).trans exactBytes⟩, remaining⟩

private theorem tailBounds {body : KBytes} {head : Buffer} {tail : List Buffer}
    (bounds : ∀ b ∈ head :: tail, b.offset + b.length ≤ body.len) :
    ∀ b ∈ tail, b.offset + b.length ≤ body.len :=
  fun b member => bounds b (List.mem_cons_of_mem _ member)

theorem packedColumns (body : KBytes) (offset : Nat) (columns : List NamedColumn)
    (descriptors : List Buffer) (bodyWF : body.wf = true)
    (bounds : ∀ b ∈ descriptors, b.offset + b.length ≤ body.len)
    (small : ∀ column ∈ columns, column.values.OffsetFits)
    (packed : PackedWire body.toList offset (columns.flatMap fun c => c.values.emit) descriptors) :
      Body.ColumnsWire body (columns.map NamedColumn.field) (columns.map NamedColumn.node)
        descriptors (columns.map fun c => c.values.observe) := by
  induction columns generalizing offset descriptors with
  | nil => cases descriptors <;> exact packed
  | cons column columns ih =>
    have headWire := emitColumn_wire column (fun values eq => by
      have fits := small column (by simp)
      rwa [eq] at fits)
    have tailSmall (c : NamedColumn) (h : c ∈ columns) : c.values.OffsetFits :=
      small c (List.mem_cons_of_mem _ h)
    rcases column with ⟨name, nullable, values⟩
    cases values with
    | int32 values =>
      let bits := emitBitmap values
      let words := emitWords 4 (values.map fun v => (v.getD 0).toUInt32.toNat)
      let next := offset + bits.len + padding bits.len
      change PackedWire body.toList offset (bits :: words :: _) descriptors at packed
      obtain ⟨tail, rfl, bitmapEq, remaining⟩ :=
        pullPiece bodyWF (emitWords_wf _ _) bounds packed
      obtain ⟨tail, rfl, dataEq, remaining⟩ :=
        pullPiece bodyWF (emitWords_wf _ _) (tailBounds bounds) remaining
      exact ⟨.int32 (Body.sliceBuffer body ⟨offset, bits.len⟩)
        (Body.sliceBuffer body ⟨next, words.len⟩), tail, rfl,
        int32Transfer bitmapEq dataEq headWire,
        ih _ _ (tailBounds (tailBounds bounds)) tailSmall remaining⟩
    | utf8 values =>
      let bits := emitBitmap values
      let offsets := emitWords 4 (utf8OffsetWords 0 values)
      let bytes := emitWords 1 ((values.flatMap utf8Part).map UInt8.toNat)
      let next := offset + bits.len + padding bits.len
      let dataStart := next + offsets.len + padding offsets.len
      change PackedWire body.toList offset (bits :: offsets :: bytes :: _) descriptors at packed
      obtain ⟨tail, rfl, bitmapEq, remaining⟩ :=
        pullPiece bodyWF (emitWords_wf _ _) bounds packed
      obtain ⟨tail, rfl, offsetsEq, remaining⟩ :=
        pullPiece bodyWF (emitWords_wf _ _) (tailBounds bounds) remaining
      obtain ⟨tail, rfl, dataEq, remaining⟩ :=
        pullPiece bodyWF (emitWords_wf _ _) (tailBounds (tailBounds bounds)) remaining
      exact ⟨.utf8 (Body.sliceBuffer body ⟨offset, bits.len⟩)
        (Body.sliceBuffer body ⟨next, offsets.len⟩) (Body.sliceBuffer body ⟨dataStart, bytes.len⟩),
        tail, rfl, utf8Transfer bitmapEq offsetsEq dataEq headWire,
        ih _ _ (tailBounds (tailBounds (tailBounds bounds))) tailSmall remaining⟩

end Silmaril.Proofs.Formats.Arrow.Writer
