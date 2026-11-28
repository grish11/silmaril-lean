module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Chain.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.ChainProofs

open CarriedAddress.Institution.RuntimeEntry (Entry)
open Silmaril.MLIR.MemRef (Buffer)
open Linked.Satisfaction.ReductImage (CaptureChain)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q : EntrySignature} {cells : Nat}

theorem mapProgramChain_eq (program : Program P) (chain : CaptureChain P Q) :
    program.mapChain chain = program.map chain.composite := by
  induction chain with
  | nil => exact (Program.map_id program).symm
  | cons head tail ih => exact (ih (program.map head)).trans (program.map_comp head tail.composite).symm

set_option backward.isDefEq.respectTransparency false in
theorem runMemRef_chain_fibre (program : Program P) (chain : CaptureChain P Q)
    (left right : Entry Q.args cells) (same : left.reduct chain.composite = right.reduct chain.composite)
    (fuel : Nat) :
    (program.mapChain chain).runMemRef left.model fuel (Buffer.mk left.heap) =
      (program.mapChain chain).runMemRef right.model fuel (Buffer.mk right.heap) := by
  rw [mapProgramChain_eq, Program.runMemRef_map, Program.runMemRef_map]
  have input := congrArg (fun entry : Entry P.args cells => entry.input) same
  have heap : left.heap = right.heap := congrArg (fun entry : Entry P.args cells => entry.heap) same
  change program.runMemRef ⟨cells, (left.reduct chain.composite).input⟩ fuel ⟨left.heap⟩ =
    program.runMemRef ⟨cells, (right.reduct chain.composite).input⟩ fuel ⟨right.heap⟩
  rw [input, heap]

set_option backward.isDefEq.respectTransparency false in
theorem numbered_observe_chain_fibre (program : Program P) (chain : CaptureChain P Q)
    (left right : Entry Q.args cells) (same : left.reduct chain.composite = right.reduct chain.composite) :
    (program.mapChain chain).numberedObserve left.model left.heap =
      (program.mapChain chain).numberedObserve right.model right.heap := by
  rw [mapProgramChain_eq, Program.numbered_observe_map, Program.numbered_observe_map]
  let observe (entry : Entry P.args cells) : Part (RVSDG.Tuple (WireVal cells) (carrier [.word, .word, .word])) :=
    program.numberedObserve entry.model entry.heap
  exact congrArg observe same

theorem mapChain_eq (sentence : Sentence P) (chain : CaptureChain P Q) :
    sentence.mapChain chain = sentence.map chain.composite := by
  induction chain with
  | nil => exact (Sentence.map_id sentence).symm
  | cons head tail ih => exact (ih (sentence.map head)).trans (sentence.map_comp head tail.composite).symm

theorem satisfaction_chain_fibre (backend : Backend) (sentence : Sentence P) (chain : CaptureChain P Q)
    (left right : Entry Q.args cells) (same : left.reduct chain.composite = right.reduct chain.composite) :
    backend.Holds (sentence.mapChain chain) left.model ↔ backend.Holds (sentence.mapChain chain) right.model := by
  simp only [mapChain_eq, backend.satisfaction_map]
  exact iff_of_eq (congrArg (fun entry : Entry P.args cells => backend.Holds sentence entry.model) same)

theorem satisfaction_liftChain (backend : Backend) (sentence : Sentence P)
    {chain : CaptureChain P Q} {source : Entry P.args cells} {stages : CaptureChain.Stages cells chain}
    (lifted : chain.lift? source = some stages) :
    backend.Holds (sentence.mapChain chain) stages.last.model ↔ backend.Holds sentence source.model := by
  obtain ⟨first, edges, _⟩ := CaptureChain.lift?_sound lifted
  have pulled : reduct chain.composite stages.last.model = source.model :=
    congrArg (Entry.model (P := P)) ((stages.first_eq_reduct_last edges).symm.trans first)
  rw [mapChain_eq, backend.satisfaction_map, pulled]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.ChainProofs
