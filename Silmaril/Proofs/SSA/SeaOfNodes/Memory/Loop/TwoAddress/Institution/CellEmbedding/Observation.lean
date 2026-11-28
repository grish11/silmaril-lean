module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellEmbedding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbeddingProofs

open CellEmbedding (Embedding extend restrict SameFrame)
open CarriedAddress.Institution.Backend (runtimeResult)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

set_option backward.isDefEq.respectTransparency false

variable {P : EntrySignature} {large : Nat}

theorem embedOutput_encode {small : Nat} (e : Embedding small large) (frame : Heap large)
    (word : Word) (final : Heap small) :
    embedOutput e frame (encodeResult word final) = encodeResult word (extend e frame final) := by
  change runtimeResult large (CellEmbedding.result e frame
    ((runtimeResult small).symm ((runtimeResult small) (word, final)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem nativeReturns_embed_iff (graph : Graph P.args) (model : EntryModel P)
    (e : Embedding model.cells large) (initial : Heap large) (word : Word) (final : Heap large) :
    nativeReturns graph (embedModel model e) initial word final ↔
      nativeReturns graph model (restrict e initial) word (restrict e final) ∧ SameFrame e initial final :=
  graph.returns_embed_iff e model.input initial word final

theorem holds_embed (s : Sentence P) (model : EntryModel P) (e : Embedding model.cells large) :
    s.Holds (embedModel model e) ↔ s.Holds model := by
  cases s with
  | equation lhs rhs =>
    constructor
    · intro holds initial word final
      let frame : Heap large := fun _ => 0
      exact (lhs.returns_extend e frame model.input initial word final).symm.trans
        ((holds (extend e frame initial) word (extend e frame final)).trans
          (rhs.returns_extend e frame model.input initial word final))
    · intro holds initial word final
      exact (nativeReturns_embed_iff lhs model e initial word final).trans
        ((and_congr_left fun _ => holds (restrict e initial) word (restrict e final)).trans
          (nativeReturns_embed_iff rhs model e initial word final).symm)
  | terminates graph =>
    constructor
    · intro holds initial
      let largeInitial := extend e (fun _ => 0) initial
      obtain ⟨word, final, returned⟩ := holds largeInitial
      refine ⟨word, restrict e final, ?_⟩
      have observed := ((nativeReturns_embed_iff graph model e largeInitial word final).mp returned).1
      simpa only [largeInitial, CellEmbedding.restrict_extend] using observed
    · intro holds initial
      obtain ⟨word, final, returned⟩ := holds (restrict e initial)
      refine ⟨word, extend e initial final, ?_⟩
      have observed := (graph.returns_extend e initial model.input (restrict e initial) word final).mpr returned
      simpa only [nativeReturns, embedModel, CellEmbedding.extend_restrict] using observed

theorem observe_embed (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel P)
    (e : Embedding model.cells large) (initial : Heap large) :
    p.observe (embedModel model e) initial =
      (p.observe model (restrict e initial)).map (embedOutput e initial) := by
  rcases Part.eq_none_or_eq_some (p.observe model (restrict e initial)) with absent | ⟨raw, observed⟩
  · rw [absent, Part.map_none, Part.eq_none_iff]
    intro target observed
    obtain ⟨⟨word, final⟩, rfl⟩ := (runtimeResult large).surjective target
    have largeReturn := (p.observe_eq_some_iff_native (embedModel model e) initial word final).mp
      (Part.eq_some_iff.mpr observed)
    have smallReturn := ((nativeReturns_embed_iff p.source model e initial word final).mp largeReturn).1
    have impossible := (p.observe_eq_some_iff_native model (restrict e initial) word (restrict e final)).mpr smallReturn
    rw [absent] at impossible
    exact Part.none_ne_some _ impossible
  · obtain ⟨⟨word, final⟩, rfl⟩ := (runtimeResult model.cells).surjective raw
    change p.observe model (restrict e initial) = Part.some (encodeResult word final) at observed
    rw [observed, Part.map_some, embedOutput_encode]
    apply (p.observe_eq_some_iff_native (embedModel model e) initial word (extend e initial final)).mpr
    have smallReturn := (p.observe_eq_some_iff_native model (restrict e initial) word final).mp observed
    have largeReturn := (p.source.returns_extend e initial model.input (restrict e initial) word final).mpr smallReturn
    simpa only [nativeReturns, embedModel, CellEmbedding.extend_restrict] using largeReturn

theorem memRef_no_return_embed (p : MemRefRoom.GeneratedProgram P.args) (model : EntryModel P)
    (e : Embedding model.cells large) (initial : Buffer large) :
    (∀ word final, ¬ p.Returns (embedModel model e) initial (word, final)) ↔
      ∀ word final, ¬ p.Returns model ⟨restrict e initial.cell⟩ (word, final) := by
  constructor
  · intro absent word ⟨final⟩ returned
    have smallReturn := (p.returns_iff_native model ⟨restrict e initial.cell⟩ word ⟨final⟩).mp returned
    have largeReturn := (p.source.returns_extend e initial.cell model.input (restrict e initial.cell) word final).mpr smallReturn
    rw [CellEmbedding.extend_restrict] at largeReturn
    exact absent word ⟨extend e initial.cell final⟩
      ((p.returns_iff_native (embedModel model e) initial word ⟨extend e initial.cell final⟩).mpr largeReturn)
  · intro absent word ⟨final⟩ returned
    have largeReturn := (p.returns_iff_native (embedModel model e) initial word ⟨final⟩).mp returned
    have smallReturn := ((nativeReturns_embed_iff p.source model e initial.cell word final).mp largeReturn).1
    exact absent word ⟨restrict e final⟩
      ((p.returns_iff_native model ⟨restrict e initial.cell⟩ word ⟨restrict e final⟩).mpr smallReturn)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbeddingProofs
