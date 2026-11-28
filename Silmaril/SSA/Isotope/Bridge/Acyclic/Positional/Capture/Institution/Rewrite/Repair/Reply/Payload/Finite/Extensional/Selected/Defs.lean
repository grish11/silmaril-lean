module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.Thms

/-! # The selected packed LambdaSSA arrows at the witnessed interface -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected

open CategoryTheory
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement (ReadTree replyContext)
open LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta (denoteArrow)
open LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

local instance : HasTy signature.Instr Sorts := signature.hasTy

/-- Keep the scope index and the entire ordered exit list of the selected
tree when using its published native LetCase witness. -/
def witnessed {L : List Sorts} {n : Nat} (p : ReadTree L n) : Source L n :=
  .tree p.witnessed

/-- In the payload separator's Freyd model, interpret the actual selected,
elaborated, and packed singleton arrow from the full native reply product. -/
noncomputable def denotation {L : List Sorts} {n : Nat} (p : ReadTree L n) :
    (J).obj ((M).obj (replyContext n)) ⟶ (J).obj ((M).obj (packedExitType L)) :=
  letI := Kleisli.instructions model
  let := modelCoherent
  denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)

def equation (H : Sorts) (L : List Sorts) {n : Nat} (p q : ReadTree (H :: L) n) : GrammarEquation signature :=
  Extensional.equation H L (witnessed p) (witnessed q)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected
