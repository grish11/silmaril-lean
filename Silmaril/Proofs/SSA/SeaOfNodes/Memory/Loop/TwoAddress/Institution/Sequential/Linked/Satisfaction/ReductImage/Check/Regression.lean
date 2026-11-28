module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Triple.Satisfaction renaming Program → TripleProgram
open Triple.Satisfaction (corridor corridor_modelExpansive_iff_check)
open Sequential.Fixture (captures graph initial)
open Linked.Fixture (combined first wiring inputs)
open Triple.Fixture (thirdWiring entryModel)

private abbrev extended : EntrySignature := ⟨.word :: combined.args⟩
private def insert : combined ⟶ extended := ⟨fun port => .tail port⟩

private def identifyStore : combined ⟶ combined :=
  ⟨fun
    | .tail (.tail (.tail (.tail (.tail (.tail .head))))) => .tail (.tail (.tail .head))
    | port => port⟩

#guard checkExpansive insert
#guard checkNoIdentification identifyStore .address
#guard !checkNoIdentification identifyStore .word
#guard !checkCoverage identifyStore 6

private theorem insertExpansive : (corridor .memref insert).ModelExpansive :=
  (corridor_modelExpansive_iff_check .memref insert).mpr rfl

example (premises : Set (Triple.Satisfaction.Sentence combined)) (sentence : Triple.Satisfaction.Sentence combined) :
    (Triple.Satisfaction.room .memref combined).Entails premises sentence ↔
      (Triple.Satisfaction.room .memref extended).Entails ((corridor .memref insert).sen '' premises)
        ((corridor .memref insert).sen sentence) :=
  (corridor .memref insert).entails_map_iff insertExpansive premises sentence

example : ¬ (corridor .coloured identifyStore).ModelExpansive :=
  fun expands => (by decide : checkExpansive identifyStore ≠ true)
    ((corridor_modelExpansive_iff_check .coloured identifyStore).mp expands)

private def insertedInput : Tuple (Val 6) extended.args := .cons (0 : Word) inputs

example : reduct insert ⟨6, insertedInput⟩ = ⟨6, inputs⟩ :=
  liftInput?_sound insert (show liftInput? insert inputs = some insertedInput from rfl)

-- The fixture supplies different values, 11 and 22, at the two identified store ports.
#guard !(liftInput? identifyStore inputs).isSome

example : ¬ InReductImage identifyStore inputs :=
  fun image => (by decide : (liftInput? identifyStore inputs).isSome ≠ true)
    ((liftInput?_isSome_iff identifyStore inputs).mpr image)

-- Identifying those same ports admits the tuple when both store values agree.
#guard (liftInput? identifyStore (reduct identifyStore entryModel).input).isSome

private def original : TripleProgram combined := ⟨⟨captures, first, graph, wiring⟩, captures, graph, thirdWiring⟩

private def runLifted : Option (Word × Word × Word × List Word) := do
  let input ← liftInput? insert inputs
  let (firstWord, secondWord, thirdWord, buffer) ← (original.map insert).runMemRef ⟨6, input⟩ 11 ⟨initial⟩
  pure (firstWord, secondWord, thirdWord, (List.finRange 6).map buffer.cell)

#guard runLifted == some (3, 3, 22, [11, 73, 11, 3, 91, 22])

private abbrev wordOnly : EntrySignature := ⟨[.word]⟩
private abbrev addressWord : EntrySignature := ⟨[.address, .word]⟩
private def insertAddress : wordOnly ⟶ addressWord :=
  ⟨fun
    | .head => .tail .head
    | .tail impossible => nomatch impossible⟩

private def zeroInput : Tuple (Val 0) wordOnly.args := .cons (7 : Word) .nil

-- An injective map can fail to lift at zero cells because the new address is empty.
#guard checkNoIdentification insertAddress .word
#guard !checkCoverage insertAddress 0
#guard checkCoverage insertAddress 1
#guard !checkExpansive insertAddress
#guard !(liftInput? insertAddress zeroInput).isSome
#guard !checkCompositeCoverage (𝟙 wordOnly) insertAddress 0
#guard checkCompositeCoverage (𝟙 wordOnly) insertAddress 1

#guard match diagnoseCompositeCoverage? (𝟙 wordOnly) insertAddress 0 with
  | some diagnostic =>
    match diagnostic.failure with
    | .emptyTargetAddress port =>
      Quads.slot port == 0 && !(liftThrough? (𝟙 wordOnly) insertAddress ⟨diagnostic.input, fun _ => 0⟩).isSome
    | _ => false
  | none => false

#guard !(diagnoseCompositeCoverage? (𝟙 wordOnly) insertAddress 1).isSome

private abbrev wordAddress : EntrySignature := ⟨[.word, .address]⟩
private def swapPorts : addressWord ⟶ wordAddress :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail impossible) => nomatch impossible⟩

private def addressSuffix : CaptureChain addressWord wordAddress := .cons swapPorts (.nil wordAddress)
private def addressChain : CaptureChain wordOnly wordAddress := .cons insertAddress addressSuffix

example : ¬ ∃ stages : CaptureChain.Stages 0 addressSuffix, stages.Compatible :=
  fun stages => (by decide : admitsInput 0 wordAddress.args ≠ true)
    ((addressSuffix.admitsStages_iff 0).mp stages)

#guard addressSuffix.checkCoverage 0
#guard !addressChain.checkCoverage 0
#guard addressChain.checkCoverage 1
#guard !(addressChain.lift? ⟨zeroInput, fun _ => 0⟩).isSome
#guard match addressChain.diagnose? 0 with
  | some diagnostic =>
    match diagnostic.failure with
    | .emptyTargetAddress port =>
      Quads.slot port == 1 && !(addressChain.lift? ⟨diagnostic.input, fun _ => 0⟩).isSome
    | _ => false
  | none => false

private abbrev twoAddresses : EntrySignature := ⟨[.address, .address]⟩
private abbrev oneAddress : EntrySignature := ⟨[.address]⟩
private def identifyAddress : twoAddresses ⟶ oneAddress :=
  ⟨fun
    | .head | .tail .head => .head
    | .tail (.tail impossible) => nomatch impossible⟩

private def singletonInput : Tuple (Val 1) twoAddresses.args :=
  .cons (0 : Address 1) (.cons (0 : Address 1) .nil)
private def distinctInput : Tuple (Val 2) twoAddresses.args :=
  .cons (0 : Address 2) (.cons (1 : Address 2) .nil)

-- At zero cells the source has no valuations. At one cell both addresses
-- must agree. Two cells are enough to witness the identification.
#guard checkCoverage identifyAddress 0
#guard checkCoverage identifyAddress 1
#guard !checkCoverage identifyAddress 2
#guard (liftInput? identifyAddress singletonInput).isSome
#guard !(liftInput? identifyAddress distinctInput).isSome
#guard checkCompositeCoverage (𝟙 twoAddresses) identifyAddress 0
#guard checkCompositeCoverage (𝟙 twoAddresses) identifyAddress 1
#guard !checkCompositeCoverage (𝟙 twoAddresses) identifyAddress 2

#guard !(diagnoseCompositeCoverage? (𝟙 twoAddresses) identifyAddress 0).isSome
#guard !(diagnoseCompositeCoverage? (𝟙 twoAddresses) identifyAddress 1).isSome
#guard match diagnoseCompositeCoverage? (𝟙 twoAddresses) identifyAddress 2 with
  | some diagnostic =>
    match diagnostic.failure with
    | .collision .address left right =>
      let leftValue : Address 2 := diagnostic.input.get left
      let rightValue : Address 2 := diagnostic.input.get right
      leftValue == 0 && rightValue == 1 &&
        !(liftThrough? (𝟙 twoAddresses) identifyAddress ⟨diagnostic.input, fun _ => 0⟩).isSome
    | _ => false
  | none => false

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage
