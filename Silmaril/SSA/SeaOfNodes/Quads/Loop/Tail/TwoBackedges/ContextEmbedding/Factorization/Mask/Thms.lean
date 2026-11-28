module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Mask.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Mask

/-! The typed mask renaming inverts the embedding at its retained positions. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization

open SeaOfNodes.Diamond (ValueSort dataPorts)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port)
open Blocks.Prune (Mask)
open Identification (PortMap)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {regs : List (ValueSort Width)}
variable {t : SeaOfNodes.Diamond.Ty Width}

theorem maskEmbedding_rename (mask : Mask regs) (target : Port (dataPorts regs) t)
    (kept : Port (dataPorts mask.kept) t) :
    mask.rename target = some kept ↔ (maskEmbedding mask).portMap t kept = target :=
  Proofs.maskEmbedding_rename mask target kept

theorem usedMask_hit (map : PortMap S T) (target : Port (dataPorts T.regs) t) :
    ((usedMask map).rename target).isSome ↔ ∃ source, map t source = target :=
  Proofs.usedMask_hit map target

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization
