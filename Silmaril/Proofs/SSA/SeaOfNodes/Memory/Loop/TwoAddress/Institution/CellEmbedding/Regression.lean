module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open RVSDG (Port)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open CellEmbedding (Embedding extend restrict)

private abbrev captures : EntrySignature := ⟨[.address, .address, .word, .word]⟩

private def stop : Port (activationArgs captures.args) .word := .tail (.tail (.tail (.tail .head)))
private def storeWord : Port (activationArgs captures.args) .word := .tail (.tail (.tail (.tail (.tail .head))))

-- Return the old first cell for the tail test and write eleven into it.
-- Feedback swaps the two old lanes, so the second activation writes the other cell.
private def graph : Graph captures.args :=
  ⟨⟨.load (.latest 0) (.arg .head)
      (.store (.latest 0) (.arg .head) (.arg storeWord)
        (.ret (.latest 1) (.output 0 .head))),
    rfl, stop⟩, .head, .tail .head, .tail .head, .head⟩

private def skipMiddle : Embedding 2 3 where
  toFun address := ⟨2 * address.val, by omega⟩
  inj' := by
    intro a b equal
    apply Fin.ext
    have numbers := congrArg Fin.val equal
    change 2 * a.val = 2 * b.val at numbers
    omega

private abbrev model : EntryModel captures :=
  ⟨2, .cons (0 : Address 2) (.cons (1 : Address 2) (.cons (0 : Word) (.cons (11 : Word) .nil)))⟩

private def initial : Heap 2 := fun cell => if cell = 0 then 7 else 0
private def afterFirst : Heap 2 := initial.write 0 11
private def final : Heap 2 := afterFirst.write 1 11
private def larger : Heap 3 := extend skipMiddle (fun _ => 73) initial

private theorem smallReturn : nativeReturns graph model initial 0 final := ⟨1, rfl⟩

example : graph.step (embedModel model skipMiddle).input
    (graph.seed (embedModel model skipMiddle).input larger) =
      .inr ⟨(2 : Address 3), (0 : Address 3), extend skipMiddle (fun _ => 73) afterFirst⟩ := by
  change graph.step (CellEmbedding.input skipMiddle model.input)
    (graph.seed (CellEmbedding.input skipMiddle model.input) (extend skipMiddle (fun _ => 73) initial)) = _
  rw [graph.seed_embed, graph.step_embed]
  rfl

-- Use the actual generated observation over the linked coloured net.
private def numbered := RuntimeRoom.GeneratedProgram.lower graph

example : numbered.petriObserve (embedModel model skipMiddle) larger =
    Part.some (encodeResult 0 (extend skipMiddle larger final)) := by
  have smallObserved : numbered.observe model (restrict skipMiddle larger) = Part.some (encodeResult 0 final) :=
    (numbered.observe_eq_some_iff_native model _ 0 final).mpr (by
      change nativeReturns graph model (restrict skipMiddle larger) 0 final
      simpa only [larger, CellEmbedding.restrict_extend] using smallReturn)
  rw [numbered.petriObserve_embed model skipMiddle larger,
    numbered.petriObserve_eq_numbered model (restrict skipMiddle larger),
    smallObserved, Part.map_some, embedOutput_encode]

private def summarize (out : Option (Word × Buffer 3)) : Option (Word × Word × Word × Word) :=
  out.map fun (word, buffer) => (word, buffer.cell 0, buffer.cell 1, buffer.cell 2)

-- The emitted MemRef CFG needs one backedge and leaves the extra cell intact.
#guard (MemRef.run graph (embedModel model skipMiddle).input 0 ⟨larger⟩).isNone
#guard summarize (MemRef.run graph (embedModel model skipMiddle).input 1 ⟨larger⟩) ==
  some (0, 11, 73, 11)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
