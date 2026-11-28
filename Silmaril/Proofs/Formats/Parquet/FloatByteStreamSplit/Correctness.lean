module

public import Silmaril.Formats.Parquet.FloatByteStreamSplit.Defs
import all Silmaril.Formats.Parquet.FloatByteStreamSplit.Defs
import Silmaril.Formats.Parquet.ByteStreamSplitPage.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.FloatByteStreamSplit

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FloatByteStreamSplit

private theorem bind_ok {ε α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

private theorem mapError_ok {ε δ α : Type} {input : Except ε α} {f : ε → δ} {out : α}
    (success : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => cases success; rfl

private theorem mapM_order {ε α β : Type} (f : α → Except ε β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      List.Forall₂ (fun x y => f x = .ok y) xs ys
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by
    rw [List.mapM_cons] at h
    obtain ⟨_, head, h⟩ := bind_ok h
    obtain ⟨_, tail, h⟩ := bind_ok h
    cases h
    exact .cons head (mapM_order f tail)

private theorem bindLeaf_ok {name : String} {schema : List Footer.SchemaElement} {leaf : Footer.SchemaElement}
    (bound : bindLeaf name schema = .ok leaf) :
    ∃ root, schema = [root, leaf] ∧ IsFlatFloat root leaf ∧ leaf.name = name := by
  rcases schema with _ | ⟨root, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [bindLeaf] at bound <;> try contradiction
  split at bound <;> try contradiction
  rename_i admitted
  split at bound <;> try contradiction
  rename_i named
  cases bound
  exact ⟨root, rfl, not_not.mp admitted, not_not.mp named⟩

private theorem matchColumn_ok {limits : Limits} {index : Nat} {leaf : Footer.SchemaElement}
    {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    (matched : matchColumn limits index leaf group = .ok column) :
    group.columns = [column] ∧ column.metadata.pathInSchema = [leaf.name] ∧
    column.metadata.physicalType = .float ∧ column.metadata.codec = 0 ∧
    column.metadata.numValues = group.numRows := by
  unfold matchColumn at matched
  split at matched <;> try contradiction
  rename_i actual shape
  dsimp only at matched
  split at matched <;> try contradiction
  rename_i path
  split at matched <;> try contradiction
  rename_i physical
  split at matched <;> try contradiction
  rename_i count
  split at matched <;> try contradiction
  rename_i codec
  split at matched <;> try contradiction
  split at matched <;> try contradiction
  split at matched <;> try contradiction
  cases matched
  exact ⟨shape, not_not.mp path, not_not.mp physical, not_not.mp codec, not_not.mp count⟩

private theorem planFrame_ok {limits : Limits} {index : Nat} {entry : Page.Frame × Nat} {plan : Plan}
    (planned : planFrame limits index entry = .ok plan) :
    plan.frame = entry.1 ∧ pageParameters entry.1.value = some plan.params := by
  unfold planFrame at planned
  dsimp only at planned
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  rename_i params projected
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  cases planned
  exact ⟨rfl, projected⟩

private theorem decodeFrame_wire {limits : Limits} {index : Nat} {source : Bytes} {leaf : Footer.SchemaElement}
    {plan : Plan} {slots : List (Option UInt32)}
    (projected : pageParameters plan.frame.value = some plan.params)
    (decoded : decodeFrame limits source leaf index plan = .ok slots) :
    PageWire limits source plan.frame slots := by
  unfold decodeFrame at decoded
  dsimp only at decoded
  obtain ⟨⟨kind, values⟩, decoded, returned⟩ := bind_ok decoded
  have decoded := mapError_ok decoded
  cases kind <;> try contradiction
  case floatBits =>
    cases returned
    obtain ⟨encoding, _, layout, page, words, valid, wire, admission, lanes, mask, bits⟩ :=
      ByteStreamSplitPage.decode_wire_sound decoded
    obtain ⟨count, present⟩ := ByteStreamSplitPage.decode_counts decoded
    exact ⟨plan.params, layout, page, words, projected, encoding, valid, wire, admission, lanes,
      mask, bits, count, present⟩

private theorem orderedPages {limits : Limits} {index : Nat} {source : Bytes} {leaf : Footer.SchemaElement}
    {entries : List (Page.Frame × Nat)} {plans : List Plan} {pages : List (List (Option UInt32))}
    (prepared : List.Forall₂ (fun entry plan => planFrame limits index entry = .ok plan) entries plans)
    (decoded : List.Forall₂ (fun plan slots => decodeFrame limits source leaf index plan = .ok slots) plans pages) :
    List.Forall₂ (fun entry slots => PageWire limits source entry.1 slots) entries pages := by
  induction prepared generalizing pages with
  | nil => cases decoded; exact .nil
  | cons planned _ ih =>
    cases decoded with
    | cons head tail =>
      obtain ⟨sameFrame, params⟩ := planFrame_ok planned
      rw [← sameFrame] at params
      refine .cons ?_ (ih tail)
      rw [← sameFrame]
      exact decodeFrame_wire params head

theorem readGroup_wire {limits : Limits} {source : Bytes} {name : String} {index : Nat}
    {slots : List (Option UInt32)} (read : readGroup limits source name index = .ok slots) :
    ∃ snapshot root leaf group column chunk frames pages,
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
      snapshot.metadata.schema = [root, leaf] ∧ IsFlatFloat root leaf ∧ leaf.name = name ∧
      snapshot.groupAt index = some group ∧ group.columns = [column] ∧
      column.metadata.pathInSchema = [leaf.name] ∧ column.metadata.physicalType = .float ∧
      column.metadata.codec = 0 ∧ column.metadata.numValues = group.numRows ∧
      Page.columnSpan snapshot.footer.start column.metadata = some chunk ∧
      Page.readChunk limits.framing snapshot.bytes chunk = .ok frames ∧
      List.Forall₂ (PageWire limits snapshot.bytes) frames pages ∧
      slots = pages.flatten ∧ slots.length = group.numRows.toNat := by
  unfold readGroup at read
  split at read <;> try contradiction
  obtain ⟨snapshot, checked, read⟩ := bind_ok read
  obtain ⟨leaf, bound, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i group selected
  dsimp only at read
  split at read <;> try contradiction
  obtain ⟨column, matched, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i chunk located
  obtain ⟨frames, framed, read⟩ := bind_ok read
  obtain ⟨plans, prepared, read⟩ := bind_ok read
  split at read <;> try contradiction
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i count
  cases read
  obtain ⟨root, shape, flat, named⟩ := bindLeaf_ok bound
  obtain ⟨columns, path, physical, codec, slotCount⟩ := matchColumn_ok matched
  refine ⟨snapshot, root, leaf, group, column, chunk, frames, pages, mapError_ok checked,
    shape, flat, named, selected, columns, path, physical, codec, slotCount, located,
    mapError_ok framed, ?_, rfl, count⟩
  rw [← List.zipIdx_map_fst 0 frames, List.forall₂_map_left_iff]
  exact orderedPages (mapM_order _ prepared) (mapM_order _ decoded)

end Silmaril.Proofs.Formats.Parquet.FloatByteStreamSplit
