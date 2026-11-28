module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Composition.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open CategoryTheory
open Fixture (captures graph initial input)
open CellEmbedding (Embedding extend restrict)
open Loop.Institution.Lowering.Backends.Activation (bindAddress)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Silmaril.MLIR.MemRef (Buffer)

private abbrev rest : EntrySignature := ⟨[.address, .word]⟩

private def keepRest : rest ⟶ captures :=
  ⟨fun p => .tail (.tail p)⟩

-- First bind the second lane, then bind the first lane in front of it.
private def swapCaptures : captures ⟶ captures :=
  bindAddress (.tail .head) (bindAddress .head keepRest)

private abbrev model : EntryModel captures := ⟨4, input 1⟩

private def inner : Embedding 4 5 where
  toFun := Fin.succ
  inj' := fun _ _ equal => Fin.ext (Nat.succ.inj (congrArg Fin.val equal))

private def outer : Embedding 5 6 where
  toFun := Fin.castSucc
  inj' := fun _ _ equal => Fin.ext (congrArg (fun a : Fin 6 => a.val) equal)

private def middleHeap : Heap 5 := extend inner (fun _ => 73) initial
private def largeHeap : Heap 6 := extend outer (fun _ => 91) middleHeap

private def firstPass : Heap 4 := (initial.write 1 0).write 2 7
private def secondPass : Heap 4 := (firstPass.write 0 0).write 2 0
private def final : Heap 4 := (secondPass.write 1 0).write 2 0

example : reduct swapCaptures (embedModel (embedModel model inner) outer) =
    embedModel (reduct swapCaptures model) (inner.trans outer) := by
  rw [← embedModel_trans, reduct_embed]

-- The reversed live lanes are still distinct after both embeddings.
example : ((mapGraph swapCaptures graph).seed (embedModel model (inner.trans outer)).input largeHeap).first =
      (2 : Address 6) ∧
    ((mapGraph swapCaptures graph).seed (embedModel model (inner.trans outer)).input largeHeap).second =
      (1 : Address 6) :=
  ⟨rfl, rfl⟩

private def numbered := RuntimeRoom.GeneratedProgram.lower graph

private theorem smallObserved : numbered.petriObserve (reduct swapCaptures model)
    (restrict inner (restrict outer largeHeap)) = Part.some (encodeResult 0 final) := by
  rw [numbered.petriObserve_eq_numbered]
  apply (numbered.observe_eq_some_iff_native (reduct swapCaptures model) _ 0 final).mpr
  change graph.Returns (Memory.Diamond.Institution.pullInput
    (EntrySignature.Hom.port swapCaptures) model.input) (restrict inner (restrict outer largeHeap)) 0 final
  rw [largeHeap, CellEmbedding.restrict_extend, middleHeap, CellEmbedding.restrict_extend]
  exact ⟨2, rfl⟩

-- Run the coloured observer on the re-emitted graph and recover the exact
-- nested result, with a separate frame at each embedding.
example : (numbered.map swapCaptures).petriObserve (embedModel model (inner.trans outer)) largeHeap =
    Part.some (encodeResult 0 (extend outer largeHeap (extend inner (restrict outer largeHeap) final))) := by
  rw [numbered.petriObserve_map_embed_trans, smallObserved,
    Part.map_some, Part.map_some, embedOutput_encode, embedOutput_encode]

private def summary (out : Option (Word × Buffer 6)) : Option (Word × List Word) :=
  out.map fun (word, heap) => (word, (List.finRange 6).map heap.cell)

-- The actual CFG keeps two different new frame values and the old sentinel.
#guard (MemRef.run (mapGraph swapCaptures graph) (embedModel model (inner.trans outer)).input 1 ⟨largeHeap⟩).isNone
#guard summary (MemRef.run (mapGraph swapCaptures graph) (embedModel model (inner.trans outer)).input 2 ⟨largeHeap⟩) ==
  some (0, [73, 0, 0, 0, 42, 91])
#guard summary (MemRef.run (mapGraph swapCaptures graph) (embedModel (embedModel model inner) outer).input 2 ⟨largeHeap⟩) ==
  some (0, [73, 0, 0, 0, 42, 91])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
