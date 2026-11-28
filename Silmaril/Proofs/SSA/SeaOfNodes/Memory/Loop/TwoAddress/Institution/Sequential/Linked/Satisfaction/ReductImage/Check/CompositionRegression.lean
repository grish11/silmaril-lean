module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Chain.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Chain.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Port Tuple)
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature
open Triple.Satisfaction (Backend corridor corridor_comp_modelExpansive_iff_check corridor_modelExpansive_iff_check)
open Triple.Satisfaction renaming Program → TripleProgram, Sentence → TripleSentence
open Sequential.Fixture (captures graph initial)
open Linked.Fixture (combined first wiring inputs rightStore)
open Triple.Fixture (thirdWiring)

private abbrev extended : EntrySignature := ⟨.word :: combined.args⟩
private def insert : combined ⟶ extended := ⟨fun port => .tail port⟩

-- The second map identifies the spare source slot with the right store slot.
private def identifySpare : extended ⟶ extended :=
  ⟨fun
    | .head => .tail rightStore
    | .tail port => .tail port⟩

#guard !checkCoverage identifySpare 6
#guard !checkExpansive identifySpare
#guard checkInjectiveOnImage insert identifySpare .word
#guard checkCompositeCoverage insert identifySpare 6
#guard checkCompositeExpansive insert identifySpare
#guard !(diagnoseCompositeCoverage? insert identifySpare 6).isSome

example (backend : Backend) : (corridor backend insert ≫ corridor backend identifySpare).ModelExpansive :=
  (corridor_comp_modelExpansive_iff_check backend insert identifySpare).mpr rfl

example (backend : Backend) : ¬ (corridor backend identifySpare).ModelExpansive :=
  fun expands => (by decide : checkExpansive identifySpare ≠ true)
    ((corridor_modelExpansive_iff_check backend identifySpare).mp expands)

private def source : Entry combined.args 6 := ⟨inputs, initial⟩
private def greedy : Tuple (Val 6) extended.args := .cons (0 : Word) inputs
private def intermediate : Entry extended.args 6 := ⟨.cons (22 : Word) inputs, initial⟩
private def target : Entry extended.args 6 := ⟨greedy, initial⟩

example : liftInput? insert source.input = some greedy := rfl
example : liftInput? identifySpare greedy = none := rfl

example : (liftInput? insert source.input >>= liftInput? identifySpare) = none := rfl

example : liftInput? (insert ≫ identifySpare) source.input = some target.input := rfl

private theorem recovered : liftThrough? insert identifySpare source = some (intermediate, target) := rfl

example : intermediate.reduct insert = source ∧ target.reduct identifySpare = intermediate :=
  liftThrough?_sound insert identifySpare recovered

-- The recovered intermediate is itself accepted by the second checker.
example : liftInput? identifySpare intermediate.input = some target.input := rfl

example : ¬ InReductImage identifySpare greedy :=
  fun image => (by decide : (liftInput? identifySpare greedy).isSome ≠ true)
    ((liftInput?_isSome_iff identifySpare greedy).mpr image)

example : InReductImage (insert ≫ identifySpare) source.input :=
  (inReductImage_comp_iff_lift insert identifySpare source.input).mpr ⟨intermediate.input, rfl, rfl⟩

-- This time the identified store ports are both used by the first map.
private def leftStore : Port combined.args .word := .tail (.tail (.tail .head))

private def identifyStores : combined ⟶ combined :=
  ⟨fun
    | .tail (.tail (.tail (.tail (.tail (.tail .head))))) => leftStore
    | port => port⟩

private def identifyUsed : extended ⟶ extended :=
  ⟨fun
    | .head => .head
    | .tail port => .tail (identifyStores.port port)⟩

#guard !checkInjectiveOnImage insert identifyUsed .word
#guard !checkCompositeCoverage insert identifyUsed 6
#guard !checkCompositeExpansive insert identifyUsed

#guard match diagnoseCompositeCoverage? insert identifyUsed 6 with
  | some diagnostic =>
    match diagnostic.failure with
    | .collision .word left right =>
      let leftValue : Word := diagnostic.input.get left
      let rightValue : Word := diagnostic.input.get right
      Quads.slot left == Quads.slot leftStore && Quads.slot right == Quads.slot rightStore &&
        leftValue == 0 && rightValue == 1 &&
        !(liftThrough? insert identifyUsed ⟨diagnostic.input, initial⟩).isSome
    | _ => false
  | none => false

example {diagnostic : CoverageDiagnostic combined extended 6}
    (found : diagnoseCompositeCoverage? insert identifyUsed 6 = some diagnostic) :
    liftThrough? insert identifyUsed ⟨diagnostic.input, initial⟩ = none :=
  diagnoseCompositeCoverage?_rejects insert identifyUsed found initial

example : liftThrough? insert identifyUsed source = none := rfl

example : ¬ InReductImage (insert ≫ identifyUsed) source.input :=
  fun image => (by decide : (liftThrough? insert identifyUsed source).isSome ≠ true)
    ((liftThrough?_isSome_iff insert identifyUsed source).mpr image)

example (sentence : TripleSentence combined) :=
  sentence.room_satisfaction_comp_of_check .memref insert identifySpare 6 rfl

example (backend : Backend) (sentence : TripleSentence combined) :
    backend.Holds ((sentence.map insert).map identifySpare) target.model ↔ backend.Holds sentence source.model :=
  backend.satisfaction_liftThrough insert identifySpare sentence recovered

private def original : TripleProgram combined := ⟨⟨captures, first, graph, wiring⟩, captures, graph, thirdWiring⟩

private def runWithLift (p : TripleProgram extended) : Option (Word × Word × Word × List Word) := do
  let (_, target) ← liftThrough? insert identifySpare source
  let (firstWord, secondWord, thirdWord, buffer) ← p.runMemRef target.model 11 ⟨target.heap⟩
  pure (firstWord, secondWord, thirdWord, (List.finRange 6).map buffer.cell)

#guard runWithLift ((original.map insert).map identifySpare) == some (3, 3, 22, [11, 73, 11, 3, 91, 22])
#guard runWithLift (original.map (insert ≫ identifySpare)) == some (3, 3, 22, [11, 73, 11, 3, 91, 22])

private abbrev finalSig : EntrySignature := ⟨.word :: extended.args⟩
private def insertAgain : extended ⟶ finalSig := ⟨fun port => .tail port⟩
private def thirdStep : CaptureChain extended finalSig := .cons insertAgain (.nil finalSig)
private def coveredChain : CaptureChain combined finalSig :=
  (.cons insert (.cons identifySpare (.nil extended)) : CaptureChain combined extended).append thirdStep
private def rejectedChain : CaptureChain combined finalSig :=
  .cons insert (.cons identifyUsed thirdStep)

#guard coveredChain.checkCoverage 6
#guard !(coveredChain.diagnose? 6).isSome
#guard !(rejectedChain.checkCoverage 6)

private def stageSpareWords : Option (Word × Word × Word) := do
  let .cons _ (.cons firstIntermediate (.cons secondIntermediate (.nil final))) ← coveredChain.lift? source
    | none
  pure (firstIntermediate.input.get .head, secondIntermediate.input.get .head, final.input.get .head)

#guard stageSpareWords == some (22, 0, 0)

example : ∃ stages : CaptureChain.Stages 6 coveredChain, stages.first = source ∧ stages.Compatible :=
  (coveredChain.checkCoverage_iff_stages 6).mp rfl source

example : coveredChain.composite = (insert ≫ identifySpare) ≫ insertAgain := rfl

example (backend : Backend) (sentence : TripleSentence combined) {stages : CaptureChain.Stages 6 coveredChain}
    (lifted : coveredChain.lift? source = some stages) :
    backend.Holds (sentence.mapChain coveredChain) stages.last.model ↔ backend.Holds sentence source.model :=
  backend.satisfaction_liftChain sentence lifted

example (sentence : TripleSentence combined) :=
  sentence.room_satisfaction_chain_of_check .memref coveredChain 6 rfl

private def runChain : Option (Word × Word × Word × List Word) := do
  let lifted ← coveredChain.lift? source
  match (TripleSentence.terminates original).mapChain coveredChain with
  | .terminates emitted =>
    let (a, b, c, buffer) ← emitted.runMemRef lifted.last.model 11 ⟨lifted.last.heap⟩
    pure (a, b, c, (List.finRange 6).map buffer.cell)
  | .equation _ _ => none

#guard runChain == some (3, 3, 22, [11, 73, 11, 3, 91, 22])

#guard match rejectedChain.diagnose? 6 with
  | some diagnostic =>
    match diagnostic.failure with
    | .collision .word left right =>
      Quads.slot left == Quads.slot leftStore && Quads.slot right == Quads.slot rightStore &&
        !(rejectedChain.lift? ⟨diagnostic.input, initial⟩).isSome
    | _ => false
  | none => false

example {diagnostic : CoverageDiagnostic combined finalSig 6}
    (found : rejectedChain.diagnose? 6 = some diagnostic) :
    rejectedChain.lift? ⟨diagnostic.input, initial⟩ = none :=
  rejectedChain.diagnose?_rejects found initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage
