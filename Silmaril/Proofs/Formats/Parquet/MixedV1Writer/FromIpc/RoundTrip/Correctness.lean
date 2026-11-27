module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms
import Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Int32ByteArrayGroup
open MixedV1Writer.FromIpc
open Silmaril.Formats.Relational.NamedTable

private theorem mapM_range_exact {α ε : Type} (rows : List α) (read : Nat → Except ε α)
    (atIndex : ∀ i : Fin rows.length, read i.val = .ok (rows.get i)) :
    (List.range rows.length).mapM read = .ok rows := by
  induction rows generalizing read with
  | nil => rfl
  | cons row rest ih =>
    have head : read 0 = .ok row := atIndex ⟨0, by simp⟩
    have tail := ih (read ∘ Nat.succ) (fun i => atIndex i.succ)
    simp [List.range_succ_eq_map, List.mapM_cons, List.mapM_map, head, tail, Bind.bind, Except.bind,
      pure, Except.pure]

private theorem descriptor_exact (schema : MixedIpc.Descriptor) (ordered : schema.viewFirst = false) :
    MixedIpc.FromParquet.descriptor (field schema.integer) (field schema.binary) = schema := by
  rcases schema with ⟨first, ⟨integer, ni⟩, ⟨binary, nb⟩⟩
  change first = false at ordered
  subst first
  cases ni <;> cases nb <;> rfl

private theorem batches_exact (batches : List (List MixedIpc.Pair)) :
    (batches.map (List.map toRow)).map MixedIpc.FromParquet.groupPairs = batches := by
  have row (pair : MixedIpc.Pair) :
      ((toRow pair).1, (toRow pair).2.map Bytes.toList) = pair := by
    rcases pair with ⟨integer, binary⟩
    cases binary <;> simp [toRow]
  simp [MixedIpc.FromParquet.groupPairs, List.map_map, Function.comp_def, row]

theorem read_roundTrip {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convert source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (backward : ToIpc.convert reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed := by
  obtain ⟨actual, projection, reread, order, opened, count, indexed⟩ := convert_indexed forward
  rw [original] at reread
  cases reread
  obtain ⟨checked, groups, reverseOpen, reads, returnedOk⟩ :=
    MixedIpc.FromParquet.convert_observation backward carrier
  have sameProjection := File.openFile_projection reverseOpen
  rw [groupLimits, opened] at sameProjection
  have project := (Except.ok.inj sameProjection).symm
  have ordered := mapM_range_exact (observed.batches.map (List.map toRow))
    (projection.readGroup sink.writer.readback) (fun i => by
      let index : Fin observed.batches.length := ⟨i.val, by simpa using i.isLt⟩
      simpa [index] using (indexed index).1)
  have readsExact : groups = observed.batches.map (List.map toRow) := by
    rw [project, count, groupLimits] at reads
    simp only [List.length_map] at ordered
    exact (Except.ok.inj (reads.symm.trans ordered))
  rw [readsExact] at returnedOk
  cases observed with
  | mk descriptor batches =>
    simpa only [MixedIpc.FromParquet.observation, descriptor_exact descriptor order, batches_exact] using returnedOk

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip
