module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Rooms.Defs

/-! The factored changes commute with emission and act on sentences and valuations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Proofs

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Backend Sentence)
open Reindex.Guarded.Institution (AdmittedAt Generated Valuation emitCorridor)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {result : Width}

theorem native_sen (path : Embedding S T) (sentence : Sentence (AdmittedAt S result)) :
    path.nativeCorridor.sen sentence = sentence.map path.mapAdmitted := by
  induction path with
  | id _ => cases sentence <;> rfl
  | permute order rest ih =>
    change rest.nativeCorridor.sen (sentence.map (Reindex.Guarded.Institution.mapAdmitted order)) = _
    rw [ih]
    cases sentence <;> rfl
  | weaken fresh rest ih =>
    change rest.nativeCorridor.sen (sentence.map (Weakening.Guarded.lift fresh)) = _
    rw [ih]
    cases sentence <;> rfl

theorem generated_sen (path : Embedding S T) (backend : Backend) (sentence : Sentence (Generated S result)) :
    (path.generatedCorridor backend).sen sentence = sentence.map path.mapGenerated := by
  induction path with
  | id _ => cases sentence <;> rfl
  | permute order rest ih =>
    change (rest.generatedCorridor backend).sen (sentence.map (Generated.map order)) = _
    rw [ih]
    cases sentence <;> rfl
  | weaken fresh rest ih =>
    change (rest.generatedCorridor backend).sen (sentence.map (Weakening.Guarded.liftGenerated fresh)) = _
    rw [ih]
    cases sentence <;> rfl

theorem native_mod (path : Embedding S T) (input : Valuation T) :
    (path.nativeCorridor (result := result)).mod.obj (Discrete.mk input) = Discrete.mk (path.reduct input) := by
  induction path with
  | id _ => rfl
  | permute order rest ih =>
    exact congrArg (Reindex.Guarded.Institution.nativeCorridor (result := result) order).mod.obj (ih input)
  | weaken fresh rest ih =>
    exact congrArg (Weakening.Guarded.nativeCorridor (result := result) fresh).mod.obj (ih input)

theorem generated_mod (path : Embedding S T) (backend : Backend) :
    (path.generatedCorridor (result := result) backend).mod = (path.nativeCorridor (result := result)).mod := by
  induction path <;> simp only [Embedding.generatedCorridor, Embedding.nativeCorridor, Room.comp_mod, *] <;> rfl

theorem emit_commutes (path : Embedding S T) (backend : Backend) :
    path.nativeCorridor (result := result) ≫ emitCorridor backend T =
      emitCorridor backend S ≫ path.generatedCorridor backend := by
  induction path with
  | id _ => simp only [Embedding.nativeCorridor, Embedding.generatedCorridor, Category.id_comp, Category.comp_id]
  | permute order rest ih =>
    simp only [Embedding.nativeCorridor, Embedding.generatedCorridor, Category.assoc, ih]
    rw [← Category.assoc, Reindex.Guarded.Institution.emit_natural, Category.assoc]
  | weaken fresh rest ih =>
    simp only [Embedding.nativeCorridor, Embedding.generatedCorridor, Category.assoc, ih]
    rw [← Category.assoc, Weakening.Guarded.emit_commutes, Category.assoc]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Proofs
