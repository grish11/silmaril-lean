module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization.Mask.Thms

/-! Compress a typed capture map to its used target bank and reinsert the unused slots. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization

open Silmaril.MLIR.Arith (Width)
open Identification (PortMap Refusal)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {result : Width}

def compressed (map : PortMap S T) : EntrySignature :=
  canonical (usedMask map).kept

/-- Every image port is kept, so old ports have a total typed renaming. -/
def compress (map : PortMap S T) : PortMap S (compressed map) :=
  fun sort port => ((usedMask map).rename (map sort port)).get ((usedMask_hit map _).mpr ⟨port, rfl⟩)

/-- Reinsert the unused ports with the existing typed context embedding. -/
def embedding (map : PortMap S T) : Embedding (compressed map) T :=
  (maskEmbedding (usedMask map)).trans (bankIdentity (canonical T.regs) T rfl)

abbrev Compared (map : PortMap S T) (result : Width) :=
  Composition.Compared (compress map) (embedding map) result

def compileStaged (map : PortMap S T) (p : AdmittedAt S result) :
    Except Refusal (Generated T result) :=
  Composition.compileStaged (compress map) (embedding map) p

/-- Run both existing checked routes for the actual computed factorization. -/
def compare (map : PortMap S T) (p : AdmittedAt S result) :
    Except Composition.Refused (Compared map result) :=
  Composition.compare (compress map) (embedding map) p

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Factorization
