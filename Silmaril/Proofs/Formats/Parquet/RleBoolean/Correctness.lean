module

public import Silmaril.Formats.Parquet.RleBoolean.Defs
import all Silmaril.Formats.Parquet.RleBoolean.Defs
import Silmaril.Formats.Parquet.RleBooleanPage.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.RleBoolean

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.RleBoolean

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

private theorem selectLeaf_ok {name : String} {schema : List Footer.SchemaElement} {leaf : Footer.SchemaElement}
    (selected : selectLeaf name schema = .ok leaf) :
    ∃ root, schema = [root, leaf] ∧ IsOptionalBoolean leaf ∧ leaf.name = name := by
  rcases schema with _ | ⟨root, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [selectLeaf] at selected <;> try contradiction
  split at selected <;> try contradiction
  rename_i optional
  split at selected <;> try contradiction
  rename_i named
  cases selected
  exact ⟨root, rfl, not_not.mp optional, not_not.mp named⟩

private theorem selectColumn_ok {limits : Limits} {leaf : Footer.SchemaElement}
    {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    (selected : selectColumn limits leaf group = .ok column) :
    group.columns = [column] ∧ ColumnMatches leaf group column ∧ column.metadata.codec = 0 := by
  unfold selectColumn at selected
  split at selected <;> try contradiction
  rename_i actual shape
  dsimp only at selected
  split at selected <;> try contradiction
  rename_i matched
  split at selected <;> try contradiction
  rename_i codec
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  cases selected
  exact ⟨shape, not_not.mp matched, not_not.mp codec⟩

private theorem planPage_ok {limits : Limits} {index : Nat} {entry : Page.Frame × Nat} {plan : Plan}
    (planned : planPage limits index entry = .ok plan) :
    plan.frame = entry.1 ∧ pageParameters entry.1.value = some plan.params := by
  unfold planPage at planned
  dsimp only at planned
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  rename_i params projected
  split at planned <;> try contradiction
  split at planned <;> try contradiction
  cases planned
  exact ⟨rfl, projected⟩

private theorem decodePage_wire {limits : Limits} {index : Nat} {source : Bytes}
    {plan : Plan} {slots : List (Option Bool)}
    (projected : pageParameters plan.frame.value = some plan.params)
    (decoded : decodePage limits source index plan = .ok slots) :
    PageWire limits source plan.frame slots := by
  unfold decodePage at decoded
  have read := mapError_ok decoded
  obtain ⟨_, encoding, layout, page, valid, wire, mask, values⟩ :=
    RleBooleanPage.decode_wire_sound read
  obtain ⟨count, _, present⟩ := RleBooleanPage.decode_counts read
  exact ⟨plan.params, layout, page, projected, encoding, valid, wire, mask, values, count, present⟩

private theorem orderedPages {limits : Limits} {index : Nat} {source : Bytes}
    {entries : List (Page.Frame × Nat)} {plans : List Plan} {pages : List (List (Option Bool))}
    (prepared : List.Forall₂ (fun entry plan => planPage limits index entry = .ok plan) entries plans)
    (decoded : List.Forall₂ (fun plan slots => decodePage limits source index plan = .ok slots) plans pages) :
    List.Forall₂ (fun entry slots => PageWire limits source entry.1 slots) entries pages := by
  induction prepared generalizing pages with
  | nil => cases decoded; exact .nil
  | cons planned _ ih =>
    cases decoded with
    | cons head tail =>
      obtain ⟨sameFrame, params⟩ := planPage_ok planned
      rw [← sameFrame] at params
      refine .cons ?_ (ih tail)
      rw [← sameFrame]
      exact decodePage_wire params head

theorem readGroup_wire {limits : Limits} {source : Bytes} {name : String} {index : Nat}
    {slots : List (Option Bool)} (read : readGroup limits source name index = .ok slots) :
    ∃ snapshot root leaf group column chunk frames pages,
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
      snapshot.metadata.schema = [root, leaf] ∧ IsOptionalBoolean leaf ∧ leaf.name = name ∧
      snapshot.groupAt index = some group ∧ group.columns = [column] ∧
      ColumnMatches leaf group column ∧ column.metadata.codec = 0 ∧
      Page.columnSpan snapshot.footer.start column.metadata = some chunk ∧
      Page.readChunk limits.framing snapshot.bytes chunk = .ok frames ∧
      List.Forall₂ (PageWire limits snapshot.bytes) frames pages ∧
      slots = pages.flatten ∧ slots.length = group.numRows.toNat := by
  unfold readGroup at read
  split at read <;> try contradiction
  obtain ⟨snapshot, checked, read⟩ := bind_ok read
  obtain ⟨leaf, selectedLeaf, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i group selectedGroup
  dsimp only at read
  split at read <;> try contradiction
  obtain ⟨column, selectedColumn, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i chunk located
  obtain ⟨frames, framed, read⟩ := bind_ok read
  obtain ⟨plans, prepared, read⟩ := bind_ok read
  split at read <;> try contradiction
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  split at read <;> try contradiction
  rename_i count
  cases read
  obtain ⟨root, shape, optional, named⟩ := selectLeaf_ok selectedLeaf
  obtain ⟨columns, matched, codec⟩ := selectColumn_ok (mapError_ok selectedColumn)
  refine ⟨snapshot, root, leaf, group, column, chunk, frames, pages, mapError_ok checked,
    shape, optional, named, selectedGroup, columns, matched, codec, located, mapError_ok framed, ?_, rfl, count⟩
  rw [← List.zipIdx_map_fst 0 frames, List.forall₂_map_left_iff]
  exact orderedPages (mapM_order _ prepared) (mapM_order _ decoded)

end Silmaril.Proofs.Formats.Parquet.RleBoolean
