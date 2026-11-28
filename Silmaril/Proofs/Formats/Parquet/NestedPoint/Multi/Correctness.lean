module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Defs
import all Silmaril.Formats.Parquet.NestedPoint.Multi.Defs
import Silmaril.Formats.Parquet.Footer.NestedLeaf.Thms
import Silmaril.Formats.Parquet.NestedPresence.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Init.Data.List.Nat.TakeDrop

namespace Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.NestedPoint (Row valueMask pairSlots)
open Silmaril.Formats.Parquet.NestedPoint.Multi

public theorem decodeFrame_wire {kind : Kind} {limits : NestedPresence.Limits} {source : Bytes}
    {frame : Page.Frame} {result : Decoded kind.Value}
    (h : decodeFrame kind limits source frame = .ok result) : FrameWire kind limits source frame result := by
  unfold decodeFrame at h
  split at h
  · cases h
  split at h
  · rename_i body payload
    cases definition : NestedPresence.decodeV1 kind.child limits frame.value body with
    | error => simp [definition, Except.mapError, bind, Except.bind] at h
    | ok decoded =>
      simp only [definition, Except.mapError, bind, Except.bind] at h
      cases plain : kind.decodePlain ((valueMask decoded).count true) decoded.scalars with
      | error => simp [plain] at h
      | ok values =>
        simp only [plain] at h
        cases reconstructed : FlatPage.reconstruct (valueMask decoded) values with
        | error => simp [reconstructed] at h
        | ok slots =>
          simp [reconstructed, pure, Except.pure] at h
          subst result
          have wire := NestedPresence.decodeV1_wire definition
          obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp reconstructed
          obtain ⟨info, kindAt, _, _, _, levelsWire⟩ := wire.page
          have statesCount : decoded.states.length = frameSlots frame := by
            simpa [frameSlots, kindAt] using levelsWire.slotCount
          have slotsCount : slots.length = decoded.states.length := by
            simpa [valueMask] using congrArg List.length mask
          exact ⟨slotsCount.trans statesCount, statesCount, body, decoded, values,
            payload, wire, rfl, plain, mask, ordered⟩
  · cases h

private theorem frames_wire (kind : Kind) (limits : NestedPresence.Limits) (source : Bytes)
    {frames : List Page.Frame} {pages : List (Decoded kind.Value)}
    (h : frames.mapM (decodeColumnFrame kind limits source) = .ok pages) :
    List.Forall₂ (FrameWire kind limits source) frames pages := by
  induction frames generalizing pages with
  | nil => cases h; exact .nil
  | cons frame tail ih =>
    simp only [List.mapM_cons] at h
    cases decoded : decodeFrame kind limits source frame with
    | error => simp [decodeColumnFrame, decoded, Except.mapError, bind, Except.bind] at h
    | ok output =>
      have one : decodeColumnFrame kind limits source frame = .ok output := by
        simp [decodeColumnFrame, decoded, Except.mapError]
      simp only [one, bind, Except.bind] at h
      cases rest : tail.mapM (decodeColumnFrame kind limits source) with
      | error => rw [rest] at h; cases h
      | ok outputs =>
        rw [rest] at h
        obtain rfl := Except.ok.inj h
        exact .cons (decodeFrame_wire decoded) (ih rest)

private theorem count_slots {kind : Kind} {limits : NestedPresence.Limits} {source : Bytes}
    {frames : List Page.Frame} {pages : List (Decoded kind.Value)}
    (wire : List.Forall₂ (FrameWire kind limits source) frames pages) :
    (concatenate pages).states.length = (frames.map frameSlots).sum ∧
      (concatenate pages).slots.length = (frames.map frameSlots).sum := by
  induction wire with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    have stateCount := head.stateCount
    have slotCount := head.slotCount
    simp only [concatenate] at ih ⊢
    simp [ih.1, ih.2, stateCount, slotCount]

public theorem readColumn_wire {kind : Kind} {limits : Limits} {snapshot : Snapshot.Checked}
    {group : Nat} {result : Decoded kind.Value} (h : readColumn kind limits snapshot group = .ok result) :
    ColumnWire kind limits snapshot group result := by
  unfold readColumn at h
  cases leafSelected : Footer.NestedLeaf.select limits.leaf.footer snapshot kind.column with
  | error => simp [leafSelected, Except.mapError, bind, Except.bind] at h
  | ok selected =>
    simp only [leafSelected, Except.mapError, bind, Except.bind] at h
    split at h
    · cases h
    rename_i profile
    have typed := not_not.mp profile
    cases chunkSelected : Footer.NestedLeaf.selectChunk selected group with
    | error => simp [chunkSelected] at h
    | ok pair =>
      obtain ⟨rowGroup, chunk⟩ := pair
      rw [chunkSelected] at h
      dsimp only at h
      split at h
      · cases h
      rename_i codec
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      rename_i metadataCount
      split at h
      · rename_i span spanAt
        split at h
        · cases h
        cases framed : Page.readChunk limits.leaf.framing snapshot.bytes span with
        | error => simp [framed] at h
        | ok frames =>
          simp only [framed] at h
          split at h
          · cases h
          rename_i total
          cases decoded : frames.mapM (decodeColumnFrame kind limits.leaf.presence snapshot.bytes) with
          | error => rw [decoded] at h; cases h
          | ok pages =>
            rw [decoded] at h
            obtain rfl := Except.ok.inj h
            have leafWire := Footer.NestedLeaf.select_wire leafSelected
            obtain ⟨groupAt, columnAt, path, physical⟩ := Footer.NestedLeaf.selectChunk_wire chunkSelected
            have wire := frames_wire kind limits.leaf.presence snapshot.bytes decoded
            have counts := count_slots wire
            have rowCount : (frames.map frameSlots).sum = rowGroup.numRows.toNat := by
              simpa using congrArg Int.toNat (not_not.mp total)
            refine ⟨selected, rowGroup, chunk, span, frames, pages, leafWire, typed.1, typed.2,
              groupAt, ?_, path, physical.trans typed.2, not_not.mp codec, not_not.mp metadataCount, spanAt,
              framed, (Page.readChunk_chain framed).2.2, wire, rfl, counts.1.trans rowCount, counts.2.trans rowCount⟩
            simpa [leafWire.ordinal] using columnAt
      · cases h

public theorem read_parentMismatch {limits : Limits} {snapshot : Snapshot.Checked} {group : Nat}
    {lhs : Decoded Int32} {rhs : Decoded Int64}
    (left : readColumn .signed limits snapshot group = .ok lhs)
    (right : readColumn .wide limits snapshot group = .ok rhs)
    (different : parentMask lhs.states ≠ parentMask rhs.states) :
    NestedPoint.Multi.read limits snapshot group = .error .parentPresence := by
  simp [NestedPoint.Multi.read, left, right, Except.mapError, bind, Except.bind, pair, different]

public theorem read_wire {limits : Limits} {snapshot : Snapshot.Checked} {group : Nat} {rows : List Row}
    (h : NestedPoint.Multi.read limits snapshot group = .ok rows) : Wire limits snapshot group rows := by
  unfold NestedPoint.Multi.read at h
  cases left : readColumn .signed limits snapshot group with
  | error => simp [left, Except.mapError, bind, Except.bind] at h
  | ok lhs =>
    simp only [left, Except.mapError, bind, Except.bind] at h
    cases right : readColumn .wide limits snapshot group with
    | error => simp [right] at h
    | ok rhs =>
      simp only [right, pair] at h
      split at h
      · rename_i parents
        obtain rfl := Except.ok.inj h
        have lw := readColumn_wire left
        have rw := readColumn_wire right
        refine ⟨⟨lhs, rhs, lw, rw, parents, rfl⟩, ?_⟩
        obtain ⟨_, lg, _, _, _, _, _, _, _, leftGroup, _, _, _, _, _, _, _, _, _, _, _, leftCount⟩ := lw.source
        obtain ⟨_, rg, _, _, _, _, _, _, _, rightGroup, _, _, _, _, _, _, _, _, _, _, _, rightCount⟩ := rw.source
        have same : lg = rg := Option.some.inj (leftGroup.symm.trans rightGroup)
        subst rg
        exact ⟨lg, leftGroup, by simp [pairSlots, leftCount, rightCount]⟩
      · cases h

end Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi
