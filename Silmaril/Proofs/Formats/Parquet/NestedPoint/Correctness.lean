module

public import Silmaril.Formats.Parquet.NestedPoint.Defs
import all Silmaril.Formats.Parquet.NestedPoint.Defs
import Silmaril.Formats.Parquet.Footer.NestedLeaf.Thms
import Silmaril.Formats.Parquet.NestedPresence.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Init.Data.List.Nat.TakeDrop

namespace Silmaril.Proofs.Formats.Parquet.NestedPoint

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.NestedPoint
open NestedPresence (Child Result)

public theorem readLeaf_wire {limits : Limits} {snapshot : Snapshot.Checked} {group column : Nat}
    {child : Child} {physical : Footer.PhysicalType} {result : Result}
    (h : readLeaf limits snapshot group column child physical = .ok result) :
    LeafWire limits snapshot group column child physical result := by
  unfold readLeaf at h
  cases selectedLeaf : Footer.NestedLeaf.select limits.footer snapshot column with
  | error => simp [selectedLeaf, Except.mapError, bind, Except.bind] at h
  | ok leaf =>
    simp only [selectedLeaf, Except.mapError, bind, Except.bind] at h
    split at h
    · cases h
    rename_i profile
    have typed := not_not.mp profile
    cases selectedChunk : Footer.NestedLeaf.selectChunk leaf group with
    | error => simp [selectedChunk] at h
    | ok pair =>
      obtain ⟨selected, chunk⟩ := pair
      rw [selectedChunk] at h
      dsimp only at h
      split at h
      · cases h
      rename_i codec
      split at h
      · cases h
      rename_i offsets
      split at h
      · rename_i span spanAt
        cases frames : Page.readChunk limits.framing snapshot.bytes span with
        | error => simp [frames] at h
        | ok pages =>
          simp only [frames] at h
          split at h
          · rename_i frame
            split at h
            · cases h
            split at h
            · rename_i body bodyAt
              cases decoded : NestedPresence.decodeV1 child limits.presence frame.value body with
              | error => simp [decoded] at h
              | ok output =>
                simp only [decoded] at h
                split at h
                · cases h
                rename_i count
                obtain rfl := Except.ok.inj h
                have shape := Footer.NestedLeaf.select_wire selectedLeaf
                obtain ⟨groupAt, chunkAt, path, phys⟩ := Footer.NestedLeaf.selectChunk_wire selectedChunk
                have absent : chunk.metadata.dictionaryPageOffset = none ∧ chunk.metadata.indexPageOffset = none := by
                  cases d : chunk.metadata.dictionaryPageOffset <;>
                    cases i : chunk.metadata.indexPageOffset <;> simp_all
                refine ⟨leaf, selected, chunk, span, frame, body, selectedLeaf, shape, typed.1,
                  typed.2, groupAt, ?_, path, phys.trans typed.2, not_not.mp codec, absent.1,
                  absent.2, spanAt, frames, (Page.readChunk_chain frames).2.2, bodyAt,
                  NestedPresence.decodeV1_wire decoded, not_not.mp count⟩
                simpa [shape.ordinal] using chunkAt
            · cases h
          · cases h
      · cases h

public theorem assemble_parentMismatch {left right : Result}
    (h : valueMask left ≠ parentMask right) : assemble left right = .error .parentPresence := by
  simp [assemble, h, throw]
  rfl

public theorem assemble_wire {left right : Result} {rows : List Row}
    (h : assemble left right = .ok rows) : AssemblyWire left right rows := by
  unfold assemble at h
  dsimp only at h
  split at h
  · cases h
  rename_i sameParents
  have parents := not_not.mp sameParents
  cases ints : Plain.decodeInt32 ((valueMask left).count true) left.scalars with
  | error => simp [ints, Except.mapError, bind, Except.bind] at h
  | ok intValues =>
    simp only [ints, Except.mapError, bind, Except.bind] at h
    cases longs : Plain.decodeInt64 ((valueMask right).count true) right.scalars with
    | error => simp [longs] at h
    | ok longValues =>
      simp only [longs] at h
      cases leftSlots : FlatPage.reconstruct (valueMask left) intValues with
      | error => simp [leftSlots] at h
      | ok lhs =>
        simp only [leftSlots] at h
        cases rightSlots : FlatPage.reconstruct (valueMask right) longValues with
        | error => simp [rightSlots] at h
        | ok rhs =>
          simp [rightSlots, pure, Except.pure] at h
          subst rows
          obtain ⟨leftShape, leftValues⟩ := FlatPage.reconstruct_ok_iff.mp leftSlots
          obtain ⟨rightShape, rightValues⟩ := FlatPage.reconstruct_ok_iff.mp rightSlots
          have lsize : lhs.length = left.states.length := by
            simpa [valueMask] using congrArg List.length leftShape
          have rsize : rhs.length = right.states.length := by
            simpa [valueMask] using congrArg List.length rightShape
          have aligned : left.states.length = right.states.length := by
            simpa [valueMask, parentMask] using congrArg List.length parents
          exact ⟨parents, by simp [pairSlots, lsize, rsize, ← aligned],
            intValues, longValues, lhs, rhs, ints, longs, leftShape, leftValues, rightShape, rightValues, rfl⟩

public theorem read_wire {limits : Limits} {snapshot : Snapshot.Checked} {group : Nat} {rows : List Row}
    (h : NestedPoint.read limits snapshot group = .ok rows) :
    ∃ left right, LeafWire limits snapshot group 0 .required .int32 left ∧
      LeafWire limits snapshot group 1 .optional .int64 right ∧ AssemblyWire left right rows := by
  unfold NestedPoint.read at h
  cases leftRead : readLeaf limits snapshot group 0 .required .int32 with
  | error => simp [leftRead, Except.mapError, bind, Except.bind] at h
  | ok left =>
    simp only [leftRead, Except.mapError, bind, Except.bind] at h
    cases rightRead : readLeaf limits snapshot group 1 .optional .int64 with
    | error => simp [rightRead] at h
    | ok right =>
      simp only [rightRead] at h
      exact ⟨left, right, readLeaf_wire leftRead, readLeaf_wire rightRead, assemble_wire h⟩

end Silmaril.Proofs.Formats.Parquet.NestedPoint
