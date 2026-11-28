module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Defs

/-! Transport entry facts under the existing injective context embeddings. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission

open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

/-- Keep old entry facts at their renamed coordinates and give each unused
capture an unconstrained fact. -/
def embedFacts : {S T : EntrySignature} → Embedding S T → EntryFacts S.regs → EntryFacts T.regs
  | _, _, .id _, facts => facts
  | _, _, .permute order rest, facts => embedFacts rest (Reindex.push order facts)
  | _, _, .weaken fresh rest, facts => embedFacts rest (Weakening.facts fresh facts)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission
