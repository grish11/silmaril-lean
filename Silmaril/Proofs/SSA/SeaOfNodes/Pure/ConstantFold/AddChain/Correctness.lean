module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain
open Diamond (Ty Val ValueSort dataPorts)
open GVN (read_weaken weaken)
open GVN.Elimination (Rewrite Routing read_splitOrigin splitOrigin)
open SubZero (model wordPort)
open Silmaril.SSA.RVSDG (Locals Tuple Wires)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}
variable {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}
variable {known : Prefix args past}

private abbrev readWord (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past)
    (wire : WordWire args past) : BitVec 64 :=
  Diamond.read model wire entry locals

private def PrefixAgrees (known : Prefix args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : Prop :=
  ConstantFold.Scan.Literals.Agrees known.literals entry locals ∧
  ∀ (wire : WordWire args past) {offset}, known.additions wire = some offset →
    readWord entry locals wire = readWord entry locals offset.base + offset.value

private theorem rightLiteral_sound {lhs rhs : WordWire args past} {offset : Offset args past}
    (agree : ConstantFold.Scan.Literals.Agrees known.literals entry locals)
    (found : known.rightLiteral? lhs rhs = some offset) :
    readWord entry locals lhs + readWord entry locals rhs = readWord entry locals offset.base + offset.value := by
  cases left : known.literals lhs <;> cases right : known.literals rhs <;>
    simp only [Prefix.rightLiteral?, left, right] at found <;> try contradiction
  split at found
  · cases found
  · obtain rfl := Option.some.inj found
    exact congrArg (readWord entry locals lhs + ·) (agree rhs right)

private theorem push_agrees (agree : PrefixAgrees known entry locals)
    {actual : BitVec 64} {literal : Option (BitVec 64)} {addition : Option (Offset args past)}
    (litSound : ∀ value, literal = some value → actual = value)
    (addSound : ∀ offset, addition = some offset → actual = readWord entry locals offset.base + offset.value) :
    PrefixAgrees (known.push literal addition) entry (locals.snoc (.cons actual .nil)) := by
  refine ⟨ConstantFold.Scan.Literals.push_agrees (out := SubZero.word) agree.1 litSound, ?_⟩
  intro wire offset found
  let next : Tuple (Val model.value) [wordPort] := .cons actual .nil
  have read := read_splitOrigin wire model entry locals next
  have weakening (original : Offset args past) :
      readWord entry (locals.snoc next) (weaken [wordPort] original.base) + original.value =
        readWord entry locals original.base + original.value :=
    congrArg (· + original.value) (read_weaken original.base model entry locals next)
  cases source : splitOrigin [wordPort] wire with
  | inl prior =>
    simp only [Prefix.push, source] at found
    obtain ⟨original, fromPrior, rfl⟩ := Option.map_eq_some_iff.mp found
    simp only [source] at read
    exact read.symm.trans ((agree.2 prior fromPrior).trans (weakening original).symm)
  | inr port =>
    cases port with
    | head =>
      simp only [Prefix.push, source] at found
      obtain ⟨original, fromNew, rfl⟩ := Option.map_eq_some_iff.mp found
      simp only [source] at read
      exact read.symm.trans ((addSound original fromNew).trans (weakening original).symm)
    | tail empty => nomatch empty

private theorem record_agrees (agree : PrefixAgrees known entry locals)
    (op : SubZero.Opcode ins out) (operands : Wires args past (dataPorts ins)) :
    PrefixAgrees (known.record op operands) entry
      (locals.snoc (.cons (model.run op (operands.read entry locals)) .nil)) := by
  cases op with
  | literal value =>
    cases operands
    exact push_agrees agree (fun _ found => Option.some.inj found) (fun _ impossible => by cases impossible)
  | sub | mul =>
    exact push_agrees agree (fun _ impossible => by cases impossible) (fun _ impossible => by cases impossible)
  | add =>
    cases operands with
    | cons lhs tail =>
      cases tail with
      | cons rhs empty =>
        cases empty
        exact push_agrees agree (fun _ impossible => by cases impossible)
          (fun _ found => rightLiteral_sound agree.1 found)

private theorem combine_sound {lhs rhs : WordWire args past} {offset : Offset args past}
    (agree : PrefixAgrees known entry locals) (found : known.combine? lhs rhs = some offset) :
    readWord entry locals lhs + readWord entry locals rhs = readWord entry locals offset.base + offset.value := by
  obtain ⟨outer, outerFound, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨inner, innerFound, found⟩ := Option.bind_eq_some_iff.mp found
  obtain rfl := Option.some.inj found
  rw [rightLiteral_sound agree.1 outerFound, agree.2 outer.base innerFound]
  exact BitVec.add_assoc _ _ _

private def sound (entry : Tuple (Val model.value) args) : ConstantFold.AddRewrite.Sound rules entry where
  Agrees facts locals := PrefixAgrees facts entry locals
  record op operands agree := record_agrees agree op operands
  replaceAdd agree accepted := by
    obtain ⟨offset, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
    rw [ConstantFold.AddRewrite.Edit.splice_eval]
    exact combine_sound agree found

variable {inputs : List (ValueSort Unit)} {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

theorem step_agrees (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) := by
  apply ConstantFold.AddRewrite.scan_agrees (sound entry) program.dataflow _ accepted
  constructor
  · intro t wire value impossible
    cases impossible
  · intro wire offset impossible
    cases impossible

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain
