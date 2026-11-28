module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Ports.Defs

/-! Embed an existing typed register mask using weakening and permutation. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization

open SeaOfNodes.Diamond (ValueSort dataPorts)
open Silmaril.MLIR.Arith (Width)
open Blocks.Prune (Mask)
open Identification (PortMap ports)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation)
open Weakening.Guarded (extend)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature}

/-- Keep the supplied first slot fixed while applying an embedding to the tail. -/
def underHead (head : ValueSort Width) : {S T : EntrySignature} →
    Embedding S T → Embedding (extend S head) (extend T head)
  | _, _, .id S => .id (extend S head)
  | _, _, @Embedding.permute _ middle _ order rest =>
    .permute (T := extend middle head) (Permutation.cons order (.value head)) (underHead head rest)
  | S, _, .weaken fresh rest =>
    .weaken fresh (.permute (T := extend (extend S fresh) head)
      (Permutation.swap (T := SeaOfNodes.Diamond.Ty Width) (.value fresh) (.value head) (dataPorts S.regs))
      (underHead head rest))

abbrev canonical (regs : List (ValueSort Width)) : EntrySignature := { regs := regs }

/-- Keep all ports in place when only the signature's equality dictionary changes. -/
def bankIdentity (S T : EntrySignature) (same : S.regs = T.regs) : Embedding S T :=
  .rename (cast (congrArg (Reindex.Registers S.regs) same) (Permutation.refl (dataPorts S.regs)))

/-- Use one weakening per omitted position and keep the retained positions in order. -/
def maskEmbedding : {regs : List (ValueSort Width)} → (mask : Mask regs) →
    Embedding (canonical mask.kept) (canonical regs)
  | _, .nil => .id _
  | _, .keep (s := head) (rest := regs) rest =>
    (bankIdentity (canonical (head :: rest.kept)) (extend (canonical rest.kept) head) rfl).trans
      ((underHead head (maskEmbedding rest)).trans
        (bankIdentity (extend (canonical regs) head) (canonical (head :: regs)) rfl))
  | _, .drop (s := head) (rest := regs) rest =>
    (maskEmbedding rest).trans
      ((Embedding.front (canonical regs) head).trans
        (bankIdentity (extend (canonical regs) head) (canonical (head :: regs)) rfl))

/-- Retain each target port hit by the supplied map, in target order. -/
def usedMask (map : PortMap S T) : Mask T.regs :=
  let slots := (ports (dataPorts S.regs)).map fun port => slot (map port.1 port.2)
  Mask.ofSlots slots.contains T.regs

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization
