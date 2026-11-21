module

public import Mathlib.Data.List.Nodup
public import Silmaril.Formats.Dasl.SparseBitmap.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.SparseBitmap

open Silmaril.Formats.Dasl.SparseBitmap
open Silmaril.Semantics (OrderedMap)

attribute [local instance] pageOrder

variable {width : Width}

theorem maskFor_bit (keys : Finset (Point width)) (index : UInt64) (offset : Offset width) :
    (maskFor keys index).getLsbD offset.val = decide ((index, offset) ∈ keys) := by
  have bound : offset.val < ((List.finRange (width.val + 1)).map
    (fun position => decide ((index, position) ∈ keys))).length := by simp
  simp only [maskFor, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem bound, Option.getD_some, List.getElem_map, List.getElem_finRange]
  rfl

theorem maskFor_nonempty (keys : Finset (Point width)) (index : UInt64) (hit : index ∈ keys.image Prod.fst) :
    maskFor keys index ≠ 0 := by
  obtain ⟨⟨found, offset⟩, present, same⟩ := Finset.mem_image.mp hit
  change found = index at same
  subst found
  intro empty
  simpa [empty, present] using maskFor_bit keys index offset

private theorem mem_points_iff (layout : Layout width) (index : UInt64) (offset : Offset width) :
    (index, offset) ∈ points layout ↔
      ∃ page, layout.lookup? index = some page ∧ page.val.getLsbD offset.val = true := by
  simp [points, offsets, List.mem_flatMap, List.mem_finRange, OrderedMap.lookup_eq_some_iff, Prod.exists,
    and_comm, and_assoc, and_left_comm]

theorem contains_iff (layout : Layout width) (point : Point width) :
    contains layout point = true ↔ point ∈ members layout := by
  rcases point with ⟨index, offset⟩
  rw [members, List.mem_toFinset, mem_points_iff]
  cases hit : layout.lookup? index <;> simp [contains, hit]

private theorem lookup_layoutFor (keys : Finset (Point width))
    (nonempty : ∀ index ∈ keys.image Prod.fst, maskFor keys index ≠ 0) (index : UInt64)
    (hit : index ∈ keys.image Prod.fst) :
    (layoutFor keys nonempty).lookup? index = some ⟨maskFor keys index, nonempty index hit⟩ := by
  apply (OrderedMap.lookup_eq_some_iff _).mpr
  refine List.mem_pmap.mpr ⟨index, (Finset.mem_sort pageOrder.le).mpr hit, rfl⟩

theorem members_layoutFor (keys : Finset (Point width))
    (nonempty : ∀ index ∈ keys.image Prod.fst, maskFor keys index ≠ 0) :
    members (layoutFor keys nonempty) = keys := by
  ext point
  rcases point with ⟨index, offset⟩
  rw [← contains_iff]
  by_cases hit : index ∈ keys.image Prod.fst
  · simp only [contains, lookup_layoutFor keys nonempty index hit, Option.map_some, Option.getD_some,
      maskFor_bit, decide_eq_true_eq]
  have missing : (layoutFor keys nonempty).lookup? index = none := by
    cases found : (layoutFor keys nonempty).lookup? index with
    | none => rfl
    | some page =>
      have entry := (OrderedMap.lookup_eq_some_iff _).mp found
      obtain ⟨other, present, equal⟩ := List.mem_pmap.mp entry
      cases congrArg Prod.fst equal
      exact False.elim (hit ((Finset.mem_sort _).mp present))
  exact iff_of_false (by simp [contains, missing]) (fun present => hit (Finset.mem_image_of_mem _ present))

private theorem page_ext {left right : Option (Page width)}
    (same : ∀ offset : Offset width,
      (left.map (fun page => page.val.getLsbD offset.val)).getD false =
      (right.map (fun page => page.val.getLsbD offset.val)).getD false) : left = right := by
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some page =>
      exact False.elim (page.property (BitVec.eq_of_getLsbD_eq_iff.mpr
        (fun bit bound => by simpa using (same ⟨bit, bound⟩).symm)))
  | some leftPage =>
    cases right with
    | none =>
      exact False.elim (leftPage.property (BitVec.eq_of_getLsbD_eq_iff.mpr
        (fun bit bound => by simpa using same ⟨bit, bound⟩)))
    | some rightPage =>
      exact congrArg some (Subtype.ext (BitVec.eq_of_getLsbD_eq_iff.mpr
        (fun bit bound => same ⟨bit, bound⟩)))

theorem ext_members {left right : Layout width} (same : members left = members right) : left = right := by
  apply OrderedMap.eq_of_lookup
  intro index
  apply page_ext
  intro offset
  change contains left (index, offset) = contains right (index, offset)
  exact Bool.eq_iff_iff.mpr (by rw [contains_iff, contains_iff, same])

private theorem points_nodup (layout : Layout width) : (points layout).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun entry _ => ?_, layout.ordered.imp ?_⟩
  · exact ((List.nodup_finRange _).filter _).map (fun _ _ same => congrArg Prod.snd same)
  · intro left right ascending point leftHit rightHit
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp leftHit
    obtain ⟨_, _, equal⟩ := List.mem_map.mp rightHit
    exact (ne_of_lt ascending) (congrArg Prod.fst equal).symm

theorem cardinality_eq (layout : Layout width) : cardinality layout = (members layout).card := by
  rw [members, List.toFinset_card_of_nodup (points_nodup layout), points, List.length_flatMap]
  simp [cardinality]

theorem pageByte_recovers (page : Page width) : pageFromByte? (pageByte page) = some page := by
  have fits : page.val.toNat < UInt8.size := page.val.isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (show width.val + 1 ≤ 8 by omega))
  simpa [pageFromByte?, pageByte, UInt8.toNat_ofNat_of_lt' fits, page.val.isLt] using page.property

end Silmaril.Proofs.Formats.Dasl.SparseBitmap
