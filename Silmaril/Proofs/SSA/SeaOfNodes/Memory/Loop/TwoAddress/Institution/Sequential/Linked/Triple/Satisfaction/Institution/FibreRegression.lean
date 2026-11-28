module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Chain.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Chain.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

open CategoryTheory
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Linked.Satisfaction.ReductImage (CaptureChain)
open Memory.Diamond.Institution renaming Signature → EntrySignature
open Sequential.Fixture (captures graph initial)
open Linked.Fixture (combined first wiring inputs secondRight)
open Triple.Fixture (thirdWiring)

private abbrev withAddress : EntrySignature := ⟨.address :: combined.args⟩
private abbrev terminal : EntrySignature := ⟨.word :: withAddress.args⟩
private def addAddress : combined ⟶ withAddress := ⟨fun port => .tail port⟩
private def addWord : withAddress ⟶ terminal := ⟨fun port => .tail port⟩
private def chain : CaptureChain combined terminal := .cons addAddress (.cons addWord (.nil terminal))

private def source : Entry combined.args 6 := ⟨inputs, initial⟩
private def firstLift : Entry terminal.args 6 :=
  ⟨.cons (22 : Word) (.cons (3 : Address 6) inputs), initial⟩
private def secondLift : Entry terminal.args 6 :=
  ⟨.cons (44 : Word) (.cons (1 : Address 6) inputs), initial⟩

private theorem same : firstLift.reduct chain.composite = secondLift.reduct chain.composite := rfl

example : firstLift.reduct chain.composite = source ∧ secondLift.reduct chain.composite = source :=
  ⟨rfl, rfl⟩

example : (chain.pullStages firstLift).Compatible ∧ (chain.pullStages secondLift).Compatible :=
  ⟨chain.pullStages_compatible _, chain.pullStages_compatible _⟩

private def original : Program combined := ⟨⟨captures, first, graph, wiring⟩, captures, graph, thirdWiring⟩
private def staged : Program terminal := original.mapChain chain

example (fuel : Nat) :
    staged.runMemRef firstLift.model fuel ⟨firstLift.heap⟩ =
      staged.runMemRef secondLift.model fuel ⟨secondLift.heap⟩ :=
  original.runMemRef_chain_fibre chain firstLift secondLift same fuel

example : staged.numberedObserve firstLift.model firstLift.heap =
    staged.numberedObserve secondLift.model secondLift.heap :=
  original.numbered_observe_chain_fibre chain firstLift secondLift same

example (backend : Backend) (sentence : Sentence combined) :
    backend.Holds (sentence.mapChain chain) firstLift.model ↔
      backend.Holds (sentence.mapChain chain) secondLift.model :=
  backend.satisfaction_chain_fibre sentence chain firstLift secondLift same

private def readMemRef (program : Program terminal) (entry : Entry terminal.args 6) (fuel : Nat) :
    Option (Word × Word × Word × List Word) :=
  (program.runMemRef entry.model fuel ⟨entry.heap⟩).map fun (a, b, c, buffer) =>
    (a, b, c, (List.finRange 6).map buffer.cell)

private def readNumbered (program : Program terminal) (entry : Entry terminal.args 6) (fuel : Nat) :
    Option (Word × Word × Word × List Word) :=
  (program.emitNumbered.graph.run (thetaRuntime 6) fuel (encodeInput entry.heap entry.input)).map fun raw =>
    let (a, b, c, heap) := (resultCodec 6).symm raw
    (a, b, c, (List.finRange 6).map heap)

#guard (readMemRef staged firstLift 10).isNone && (readMemRef staged secondLift 10).isNone
#guard readMemRef staged firstLift 11 == some (3, 3, 22, [11, 73, 11, 3, 91, 22])
#guard readMemRef staged secondLift 11 == readMemRef staged firstLift 11
#guard (readNumbered staged firstLift 1).isNone && (readNumbered staged secondLift 1).isNone
#guard readNumbered staged secondLift 2 == readMemRef staged firstLift 11
#guard readNumbered staged firstLift 2 == readNumbered staged secondLift 2

-- A target-local Boundary can read both spare ports.
private def spareWiring : Boundary.Wiring terminal.args captures.args :=
  .forward (.tail .head) (.forward (.tail (.tail secondRight)) (.word fun
    | .head => .head
    | .tail impossible => nomatch impossible))

private def readsSpares : Program terminal :=
  { staged with pair := { staged.pair with wiring := spareWiring } }

#guard readMemRef readsSpares firstLift 11 == some (3, 3, 22, [11, 73, 11, 3, 91, 22])
#guard readMemRef readsSpares secondLift 11 == some (3, 3, 44, [11, 3, 11, 9, 91, 44])
#guard readNumbered readsSpares secondLift 2 == readMemRef readsSpares secondLift 11

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction
