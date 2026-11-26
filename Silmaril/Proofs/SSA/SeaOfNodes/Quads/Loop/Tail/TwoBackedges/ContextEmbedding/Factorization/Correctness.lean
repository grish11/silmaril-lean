module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms

/-! The actual compressed map is surjective onto exactly the used typed target ports. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Proofs

open SeaOfNodes.Diamond (dataPorts)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Identification (PortMap)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {t : SeaOfNodes.Diamond.Ty Width}

set_option backward.isDefEq.respectTransparency false in
theorem embedding_rename (map : PortMap S T) (target : Port (dataPorts T.regs) t)
    (kept : Port (dataPorts (compressed map).regs) t) :
    (usedMask map).rename target = some kept ↔ (embedding map).portMap t kept = target := by
  simp only [embedding, Embedding.portMap_trans]
  exact maskEmbedding_rename (usedMask map) target kept

theorem thenMap_eq (map : PortMap S T) : Composition.thenMap (compress map) (embedding map).portMap = map := by
  funext sort port
  apply (embedding_rename map (map sort port) (compress map sort port)).mp
  exact (Option.some_get _).symm

theorem compress_surjective (map : PortMap S T) (sort : SeaOfNodes.Diamond.Ty Width) :
    Function.Surjective (compress map sort) := by
  intro kept
  let target := (embedding map).portMap sort kept
  have present : (usedMask map).rename target = some kept :=
    (embedding_rename map target kept).mpr rfl
  obtain ⟨old, hit⟩ := (usedMask_hit map target).mp (by rw [present]; rfl)
  refine ⟨old, (embedding map).portMap_injective _ ?_⟩
  exact (congrFun (congrFun (thenMap_eq map) sort) old).trans hit

theorem embedding_image (map : PortMap S T) (target : Port (dataPorts T.regs) t) :
    (∃ kept, (embedding map).portMap t kept = target) ↔ ∃ old, map t old = target := by
  have factor port := congrFun (congrFun (thenMap_eq map) t) port
  constructor
  · rintro ⟨kept, hit⟩
    obtain ⟨old, rfl⟩ := compress_surjective map t kept
    exact ⟨old, (factor old).symm.trans hit⟩
  · rintro ⟨old, hit⟩
    exact ⟨compress map t old, (factor old).trans hit⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Proofs
