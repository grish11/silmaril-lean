module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Guarded.Thms

/-! Compose the existing local observation-room corridors along an embedding. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Embedding

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Backend)
open Reindex.Guarded.Institution (nativeRoom generatedRoom)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {result : Width}

noncomputable def nativeCorridor : {S T : EntrySignature} → Embedding S T → (nativeRoom result S ⟶ nativeRoom result T)
  | _, _, .id _ => 𝟙 _
  | _, _, .permute order rest => Reindex.Guarded.Institution.nativeCorridor order ≫ rest.nativeCorridor
  | _, _, .weaken fresh rest => Weakening.Guarded.nativeCorridor fresh ≫ rest.nativeCorridor

noncomputable def generatedCorridor (backend : Backend) :
    {S T : EntrySignature} → Embedding S T → (generatedRoom result backend S ⟶ generatedRoom result backend T)
  | _, _, .id _ => 𝟙 _
  | _, _, .permute order rest =>
    Reindex.Guarded.Institution.generatedCorridor backend order ≫ rest.generatedCorridor backend
  | _, _, .weaken fresh rest => Weakening.Guarded.generatedCorridor fresh backend ≫ rest.generatedCorridor backend

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Embedding
