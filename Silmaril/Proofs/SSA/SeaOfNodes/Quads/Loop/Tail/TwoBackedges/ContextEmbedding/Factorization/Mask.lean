module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Mask.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms

/-! The embedding built from the mask inserts exactly the omitted slots. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Blocks.Prune (Mask)
open Identification (PortMap ports)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {regs : List (ValueSort Width)}
variable {t : SeaOfNodes.Diamond.Ty Width}

private theorem underHead_head (head : ValueSort Width) (path : Embedding S T) :
    (underHead head path).portMap (.value head) .head = .head := by
  induction path with
  | id => rfl
  | permute _ _ ih => exact ih
  | weaken _ _ ih => exact ih

private theorem underHead_tail (head : ValueSort Width) (path : Embedding S T) (port : Port (dataPorts S.regs) t) :
    (underHead head path).portMap t (.tail port) = .tail (path.portMap t port) := by
  induction path with
  | id => rfl
  | permute order rest ih => exact ih (order t port)
  | weaken _ rest ih => exact ih (.tail port)

-- The dependent port indices reduce through the canonical signature and mask projections.
set_option backward.isDefEq.respectTransparency false

private theorem keep_head (head : ValueSort Width) (mask : Mask regs) :
    (maskEmbedding (.keep (s := head) mask)).portMap (.value head) .head = .head := by
  simp only [maskEmbedding, Embedding.portMap_trans]
  exact underHead_head _ _

private theorem keep_tail (head : ValueSort Width) (mask : Mask regs) (port : Port (dataPorts mask.kept) t) :
    (maskEmbedding (.keep (s := head) mask)).portMap t (.tail port) =
      .tail ((maskEmbedding mask).portMap t port) := by
  simp only [maskEmbedding, Embedding.portMap_trans]
  exact underHead_tail _ _ _

private theorem drop_port (head : ValueSort Width) (mask : Mask regs) (port : Port (dataPorts mask.kept) t) :
    (maskEmbedding (.drop (s := head) mask)).portMap t port =
      .tail ((maskEmbedding mask).portMap t port) := by
  simp only [maskEmbedding, Embedding.portMap_trans]
  rfl

private theorem mask_rename_embed (mask : Mask regs) (port : Port (dataPorts mask.kept) t) :
    mask.rename ((maskEmbedding mask).portMap t port) = some port := by
  induction mask with
  | nil => exact nomatch port
  | keep rest ih =>
    cases port with
    | head =>
      rw [keep_head]
      rfl
    | tail port =>
      rw [keep_tail]
      change (rest.rename ((maskEmbedding rest).portMap t port)).map Port.tail = _
      rw [ih port]
      rfl
  | drop rest ih =>
    change Port (dataPorts rest.kept) t at port
    rw [drop_port]
    exact ih port

private theorem mask_embed_rename (mask : Mask regs) (target : Port (dataPorts regs) t)
    (kept : Port (dataPorts mask.kept) t) (hit : mask.rename target = some kept) :
    (maskEmbedding mask).portMap t kept = target := by
  induction mask with
  | nil => exact nomatch target
  | keep rest ih =>
    cases target with
    | head =>
      change some .head = some kept at hit
      obtain rfl := Option.some.inj hit
      exact keep_head _ _
    | tail target =>
      change (rest.rename target).map Port.tail = some kept at hit
      cases found : rest.rename target with
      | none => simp [found] at hit
      | some port =>
        rw [found] at hit
        obtain rfl := Option.some.inj hit
        rw [keep_tail, ih target port found]
  | drop rest ih =>
    cases target with
    | head => cases hit
    | tail target =>
      change Port (dataPorts rest.kept) t at kept
      rw [drop_port, ih target kept hit]

theorem maskEmbedding_rename (mask : Mask regs) (target : Port (dataPorts regs) t)
    (kept : Port (dataPorts mask.kept) t) :
    mask.rename target = some kept ↔ (maskEmbedding mask).portMap t kept = target :=
  ⟨mask_embed_rename mask target kept, fun h => h ▸ mask_rename_embed mask kept⟩

private theorem ofSlots_rename_isSome (slots : Nat → Bool) (target : Port (dataPorts regs) t) :
    ((Mask.ofSlots slots regs).rename target).isSome = slots (slot target) := by
  induction regs generalizing slots with
  | nil => exact nomatch target
  | cons head rest ih =>
    let tail := Mask.ofSlots (fun k => slots (k + 1)) rest
    by_cases hit : slots 0 = true
    · have shape : Mask.ofSlots slots (head :: rest) = .keep tail := by simp [Mask.ofSlots, tail, hit]
      rw [congrArg (fun m => (m.rename target).isSome) shape]
      cases target with
      | head => exact hit.symm
      | tail port =>
        simp only [Mask.rename, Option.isSome_map, slot]
        exact ih _ port
    · have shape : Mask.ofSlots slots (head :: rest) = .drop tail := by simp [Mask.ofSlots, tail, hit]
      rw [congrArg (fun m => (m.rename target).isSome) shape]
      cases target with
      | head => exact (Bool.eq_false_of_not_eq_true hit).symm
      | tail port => exact ih _ port

theorem usedMask_hit (map : PortMap S T) (target : Port (dataPorts T.regs) t) :
    ((usedMask map).rename target).isSome ↔ ∃ source, map t source = target := by
  rw [usedMask, ofSlots_rename_isSome, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨⟨sort, source⟩, _, hit⟩
    obtain ⟨rfl, same⟩ := Sigma.mk.inj_iff.mp (Reindex.slot_eq _ _ hit)
    exact ⟨source, eq_of_heq same⟩
  · rintro ⟨source, rfl⟩
    exact ⟨⟨t, source⟩, Identification.ports_complete source, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Proofs
