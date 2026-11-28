module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Defs

/-! Typed maps on the captured entry ports of the two-address profile. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open CategoryTheory Silmaril.Logic.Institution
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open CarriedAddress.Institution (liftAddress)

variable {P Q : EntrySignature}

/-- Extend the capture map beneath the two live header addresses. -/
abbrev liftAddresses (h : P ⟶ Q) :
    (⟨activationArgs P.args⟩ : EntrySignature) ⟶ ⟨activationArgs Q.args⟩ :=
  liftAddress (liftAddress h)

/-- Rename captures in the body and both operand columns. The feedback
map leaves the two old address lanes in place. -/
def mapGraph (h : P ⟶ Q) (graph : Graph P.args) : Graph Q.args where
  activation := Loop.Institution.mapGraph (liftAddresses h) graph.activation
  entryFirst := EntrySignature.Hom.port h graph.entryFirst
  entrySecond := EntrySignature.Hom.port h graph.entrySecond
  feedbackFirst := EntrySignature.Hom.port (liftAddresses h) graph.feedbackFirst
  feedbackSecond := EntrySignature.Hom.port (liftAddresses h) graph.feedbackSecond

def Sentence.map (h : P ⟶ Q) : Sentence P → Sentence Q
  | .equation lhs rhs => .equation (mapGraph h lhs) (mapGraph h rhs)
  | .terminates graph => .terminates (mapGraph h graph)

/-- A model fixes a typed input and cell count. Both sentences quantify
over all initialized heaps at that model. -/
def room (P : EntrySignature) : Room.{0, 0, 0} where
  Sen := Sentence P
  Mod := Cat.of (Discrete (EntryModel P))
  Sat m s := s.Holds m.as

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
