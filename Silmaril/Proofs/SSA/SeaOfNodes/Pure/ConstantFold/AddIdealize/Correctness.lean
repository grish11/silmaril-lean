module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize
open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (Routing dropNewest dropNewest_agrees routeSuffix routeSuffix_agrees)
open LeftSpine (SourceIds)
open RightSpine (Addends WordWire)
open SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Locals Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}
variable {ids : SourceIds} {facts : Facts args past}

private def FactsAgree (facts : Facts args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : Prop :=
  facts.analyzed.Agrees entry locals ∧ facts.explicit.Agrees entry locals

private theorem record_agrees (agree : FactsAgree facts entry locals)
    {ins : List (ValueSort Unit)} {out : ValueSort Unit} (op : SubZero.Opcode ins out)
    (operands : Wires args past (dataPorts ins)) :
    FactsAgree (facts.record op operands) entry
      (locals.snoc (.cons (model.run op (operands.read entry locals)) .nil)) :=
  ⟨RightSpine.Prefix.record_agrees agree.1 op operands, AddChain.Prefix.record_agrees agree.2 op operands⟩

variable {lhs rhs : WordWire args past} {edit : Edit args past} {rule : Rule}

private theorem checked_agrees {branch : Rule} {candidate : Option (AddRewrite.Splice args past)}
    (sound : ∀ splice, candidate = some splice → AddRewrite.evalAdd lhs rhs entry locals = splice.eval entry locals)
    (accepted : checkedSplice branch candidate = .ok (some (rule, edit))) :
    AddRewrite.evalAdd lhs rhs entry locals = edit.eval entry locals := by
  cases candidate with
  | none => cases accepted
  | some splice =>
    cases accepted
    exact sound splice rfl

private theorem leftBranch_agrees (agree : FactsAgree facts entry locals) {left : Addends args past}
    (accepted : leftBranch ids facts lhs rhs left = .ok (some (rule, edit))) :
    AddRewrite.evalAdd lhs rhs entry locals = edit.eval entry locals := by
  unfold leftBranch at accepted
  split at accepted
  · exact checked_agrees (fun _ found => AddChain.match_agrees agree.2 found) accepted
  · split at accepted
    · cases accepted
    · cases accepted
    · exact checked_agrees (fun _ found => LeftSpine.match_agrees agree.1 found) accepted

private theorem select_agrees (agree : FactsAgree facts entry locals)
    (accepted : select ids facts lhs rhs = .ok (some (rule, edit))) :
    AddRewrite.evalAdd lhs rhs entry locals = edit.eval entry locals := by
  unfold select at accepted
  split at accepted
  · rename_i value found
    cases accepted
    exact Scan.Rule.replacement_sound agree.1.1 (arithmeticRules .add) _ found
  · split at accepted
    · split at accepted
      · rename_i zero
        cases accepted
        let hint : Option (BitVec 64) := facts.explicit.literals rhs
        have tested : decide (hint = some 0) = true := zero
        have rightZero : facts.explicit.literals rhs = some (0 : BitVec 64) :=
          of_decide_eq_true (p := hint = some 0) tested
        have right := agree.2.1 rhs rightZero
        change BitVec.add (Diamond.read model lhs entry locals) (Diamond.read model rhs entry locals) = _
        rw [right]
        exact BitVec.add_zero _
      · cases accepted
    · split at accepted
      · exact checked_agrees (fun _ found => Doubling.match_agrees agree.1.1 found) accepted
      · split at accepted
        · cases accepted
        · exact checked_agrees (fun _ found => RightSpine.match_agrees agree.1 found) accepted
        · exact leftBranch_agrees agree accepted
        · split at accepted <;> cases accepted

private theorem apply_agrees (lhs rhs : WordWire args past) (edit : Edit args past)
    (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs)
    (equal : AddRewrite.evalAdd lhs rhs entry locals = edit.eval entry locals) :
    let original := Dataflow.cons SubZero.Opcode.add (.cons lhs (.cons rhs .nil)) rest
    let rewrite := edit.apply rest
    Routing.Agrees rewrite.route model entry (original.eval model entry locals)
      (rewrite.flow.eval model entry locals) := by
  cases edit with
  | replaceLiteral value =>
    have same : AddRewrite.evalAdd lhs rhs entry locals = model.run value .nil := equal
    dsimp only [Edit.apply, Routing.Agrees]
    intro t wire
    change Diamond.read model wire entry (rest.eval model entry
      (locals.snoc (.cons (AddRewrite.evalAdd lhs rhs entry locals) .nil))) =
      Diamond.read model wire entry (rest.eval model entry (locals.snoc (.cons (model.run value .nil) .nil)))
    rw [same]
  | redirect wire =>
    let next : Tuple (Val model.value) [wordPort] := .cons (AddRewrite.evalAdd lhs rhs entry locals) .nil
    exact routeSuffix_agrees rest (dropNewest wire) model entry (locals.snoc next) locals
      (dropNewest_agrees wire model entry locals next equal)
  | splice edit => exact AddRewrite.insertSplice_agrees lhs rhs edit rest equal

private theorem found_map {α β : Type} {decision : Outcome α} {value : β} (f : α → β)
    (accepted : decision.map (Option.map f) = .ok (some value)) :
    ∃ source, decision = .ok (some source) ∧ f source = value := by
  cases decision with
  | error => cases accepted
  | ok result =>
    obtain ⟨source, rfl, rfl⟩ := Option.map_eq_some_iff.mp (Except.ok.inj accepted)
    exact ⟨source, rfl, rfl⟩

variable {flow : Dataflow SubZero.Opcode args past sigs} {sort : ValueSort Unit}
variable {applied : Applied args past sigs}

private theorem atProducer_agrees (candidate : Producer flow sort) (agree : FactsAgree facts entry locals)
    (accepted : atProducer ids facts candidate = .ok (some applied)) :
    Routing.Agrees applied.rewrite.route model entry (flow.eval model entry locals)
      (applied.rewrite.flow.eval model entry locals) := by
  induction candidate with
  | @here scope sigs ins sort op operands rest =>
    cases op with
    | literal | sub | mul => cases accepted
    | add =>
      cases operands with
      | cons lhs tail =>
        cases tail with
        | cons rhs empty =>
          cases empty
          obtain ⟨⟨rule, edit⟩, found, rfl⟩ := found_map _ accepted
          exact apply_agrees lhs rhs edit rest (select_agrees agree found)
  | @later scope sigs ins out sort op operands rest candidate ih =>
    obtain ⟨rewritten, found, rfl⟩ := found_map _ accepted
    exact ih (record_agrees agree op operands) found

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out} {candidate : Producer program.dataflow word}
variable {applied : Applied (dataPorts inputs) [] program.sigs}

theorem step_agrees (accepted : step ids program candidate = .ok (some applied))
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees applied.rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (applied.rewrite.flow.eval model entry PUnit.unit) :=
  atProducer_agrees candidate ⟨RightSpine.Prefix.empty_agrees entry, AddChain.Prefix.empty_agrees entry⟩ accepted

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize
