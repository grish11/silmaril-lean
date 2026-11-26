module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Defs

/-! Three actual numbered θs linked by two statically typed boundaries. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple

open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open RVSDG.NestedTheta.ExplicitRuntime (EntryChecked)
open RVSDG.NestedTheta.ExplicitRuntime.Splice (graph graphChecked)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {ambient next last : List ValueSort} {P Q R : EntrySignature}

/-- Forward the first word through the second boundary on its own lane.
The third loop's captures read the second result and the second entry bank. -/
def carryFirst (wiring : Boundary.Wiring next last) :
    Boundary.Wiring (.word :: next) (.word :: last) :=
  .forward .head (wiring.map fun p => .tail p)

def finalStage (third : Graph last) (wiring : Boundary.Wiring next last) :=
  Boundary.splice (carryFirst wiring) (Wrapper.thirdChecked third)

def finalStageChecked (third : Graph last) (wiring : Boundary.Wiring next last) :
    EntryChecked (a := inputData (.word :: .word :: next)) (b := inputData [.word, .word, .word])
      (finalStage third wiring).toTerm :=
  graphChecked (Boundary.checked (carryFirst wiring)) (Wrapper.thirdChecked third)

def lastTwo (second : Graph next) (third : Graph last) (wiring : Boundary.Wiring next last) :=
  graph (Wrapper.forwardingChecked second (fun p => .tail p)) (finalStageChecked third wiring)

def lastTwoChecked (second : Graph next) (third : Graph last) (wiring : Boundary.Wiring next last) :
    EntryChecked (a := inputData (.word :: next)) (b := inputData [.word, .word, .word])
      (lastTwo second third wiring).toTerm :=
  graphChecked (Wrapper.forwardingChecked second (fun p => .tail p)) (finalStageChecked third wiring)

/-- Each splice substitutes the complete returned packet, including the only
live heap. The third θ returns the words in execution order. -/
def lower (first : Graph ambient) (second : Graph next) (third : Graph last)
    (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last) :
    RVSDG.NestedTheta.Graph ThetaOpcode (carrier ambient) []
      [carrier (activationArgs ambient), carrier (activationArgs next), carrier (activationArgs last)]
      (carrier [.word, .word, .word]) :=
  graph (Wrapper.producerChecked first)
    (graphChecked (Boundary.checked firstWiring) (lastTwoChecked second third secondWiring))

def checked (first : Graph ambient) (second : Graph next) (third : Graph last)
    (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last) :
    EntryChecked (a := inputData ambient) (b := inputData [.word, .word, .word])
      (lower first second third firstWiring secondWiring).toTerm :=
  graphChecked (Wrapper.producerChecked first)
    (graphChecked (Boundary.checked firstWiring) (lastTwoChecked second third secondWiring))

/-- Use the emitted graph as a program in the existing runtime observation room. -/
def program (first : Graph ambient) (second : Graph next) (third : Graph last)
    (firstWiring : Boundary.Wiring ambient next) (secondWiring : Boundary.Wiring next last) :
    RuntimeObservation.Program target (carrier ambient) (carrier [.word, .word, .word]) :=
  ⟨_, lower first second third firstWiring secondWiring⟩

abbrev Result (cells : Nat) := Word × Word × Word × Heap cells

def resultCodec (cells : Nat) : Result cells ≃ Tuple (WireVal cells) (carrier [.word, .word, .word]) where
  toFun out := Wrapper.thirdOutput out.1 out.2.1 (encodeResult out.2.2.1 out.2.2.2)
  invFun
    | .cons first (.cons second (.cons third (.cons heap .nil))) => (first, second, third, heap)
  left_inv _ := rfl
  right_inv
    | .cons _ (.cons _ (.cons _ (.cons _ .nil))) => rfl

/-- Relational composition of separately emitted observers. The first two
stages use the original sequential API, and the third reads their post-heap. -/
noncomputable def numbered (first : Graph P.args) (second : Graph Q.args) (third : Graph R.args)
    (firstWiring : Boundary.Wiring P.args Q.args) (secondWiring : Boundary.Wiring Q.args R.args)
    (model : EntryModel P) (initial : Heap model.cells) : Part (Result model.cells) :=
  (Sequential.numbered (.lower first) (.lower second) model
    (fun word => firstWiring.select word model.input) initial).bind fun (firstWord, secondWord, middle) =>
    let bank := secondWiring.select secondWord (firstWiring.select firstWord model.input)
    (numberedStage (P := R) (.lower third) ⟨model.cells, bank⟩ middle).map
      fun (word, final) => (firstWord, secondWord, word, final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple
