module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Scan
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open GVN.Elimination (read_splitOrigin splitOrigin)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)

variable {Op : Signature Unit} {m : Model Op}
variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}
variable {entry : Tuple (Val m.value) args}
variable {locals : Locals (Val m.value) past} {known : Literals m args past}

theorem push_agrees (agree : known.Agrees entry locals)
    {actual : Val m.value (.value out)} {hint : Option (Val m.value (.value out))}
    (sound : ∀ value, hint = some value → actual = value) :
    Literals.Agrees (known.push hint) entry (locals.snoc (.cons actual .nil)) := by
  intro t wire value found
  have read := read_splitOrigin wire m entry locals (.cons actual .nil)
  cases part : splitOrigin (T := Ty Unit) (past := past) [.value out] wire with
  | inl earlier =>
    simp only [Literals.push, part] at found
    exact (by simpa only [part] using read.symm : Diamond.read m wire entry _ =
      Diamond.read m earlier entry locals).trans (agree earlier found)
  | inr port =>
    cases port with
    | head =>
      simp only [Literals.push, part] at found
      exact (by simpa only [part, Tuple.get] using read.symm : Diamond.read m wire entry _ =
        actual).trans (sound value found)
    | tail rest => nomatch rest

theorem literalInputs_sound (agree : known.Agrees entry locals) {ports : List (Ty Unit)}
    (operands : Wires args past ports) {values : Tuple (Val m.value) ports}
    (found : literalInputs? known operands = some values) :
    operands.read entry locals = values := by
  induction operands with
  | nil =>
    cases Option.some.inj found
    rfl
  | cons wire rest ih =>
    obtain ⟨value, knownWire, result⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨tail, knownRest, rfl⟩ := Option.map_eq_some_iff.mp result
    change Tuple.cons (Diamond.read m wire entry locals) (Wires.read rest entry locals) = _
    rw [agree wire knownWire, ih knownRest]

theorem replacement_sound (agree : known.Agrees entry locals) {op : Op ins out}
    (rule : Rule m op) (operands : Wires args past (dataPorts ins)) {literal : Op [] out}
    (found : rule.replacement? known operands = some literal) :
    m.run op (operands.read entry locals) = m.run literal .nil := by
  induction rule with
  | literal original =>
    cases operands
    cases Option.some.inj found
    rfl
  | operation opcode encode read_encode =>
    obtain ⟨values, knownOperands, rfl⟩ := Option.map_eq_some_iff.mp found
    rw [read_encode, literalInputs_sound agree operands knownOperands]
  | sameWord opcode result read_same fallback ih =>
    cases operands with
    | cons lhs tail =>
      cases tail with
      | cons rhs empty =>
        cases empty
        simp only [Rule.replacement?, Tuple.get] at found
        split at found
        · rename_i sameAddress
          have same := Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective
            (.cons lhs .nil) (.cons rhs .nil) (congrArg (fun address => [address]) sameAddress)
          have sameWire := congrArg (fun wires => Tuple.get wires .head) same
          change lhs = rhs at sameWire
          subst rhs
          cases Option.some.inj found
          exact read_same _
        · exact ih _ found
  | commuteLeftLiteral opcode read_swapped fallback ih => exact ih operands found

theorem record_agrees (agree : known.Agrees entry locals) {op : Op ins out}
    (rule : Rule m op) (operands : Wires args past (dataPorts ins)) :
    Literals.Agrees (rule.record known operands) entry
      (locals.snoc (.cons (m.run op (operands.read entry locals)) .nil)) := by
  apply push_agrees agree
  intro value found
  obtain ⟨literal, computed, rfl⟩ := Option.map_eq_some_iff.mp found
  exact replacement_sound agree rule operands computed

private theorem orderOperands_sound {op : Op ins out}
    (rule : Rule m op) (operands : Wires args past (dataPorts ins)) :
    m.run op ((rule.orderOperands known operands).read entry locals) =
      m.run op (operands.read entry locals) := by
  induction rule with
  | literal | operation => rfl
  | sameWord opcode result read_same fallback ih => exact ih operands
  | commuteLeftLiteral opcode read_swapped fallback ih =>
    cases operands with
    | cons lhs tail =>
      cases tail with
      | cons rhs empty =>
        cases empty
        simp only [Rule.orderOperands]
        split
        · exact read_swapped (Diamond.read m lhs entry locals) (Diamond.read m rhs entry locals)
        · exact ih _

private theorem dataflow_eval (rules : Rules m) (flow : Dataflow Op args past sigs)
    (agree : known.Agrees entry locals) :
    (foldDataflow rules known flow).eval m entry locals = flow.eval m entry locals := by
  induction flow with
  | nil => rfl
  | @cons scope sigs ins out op operands rest ih =>
    cases found : (rules op).replacement? known operands with
    | none =>
      have same := orderOperands_sound (known := known) (entry := entry) (locals := locals) (rules op) operands
      simp only [foldDataflow, found, Dataflow.eval, same]
      exact ih (push_agrees agree (by intro value impossible; cases impossible))
    | some literal =>
      have same := replacement_sound agree (rules op) operands found
      simp only [foldDataflow, found, Dataflow.eval]
      calc
        _ = rest.eval m entry (locals.snoc (.cons (m.run literal .nil) .nil)) :=
          ih (push_agrees agree (fun _ foundValue => Option.some.inj foundValue))
        _ = _ := congrArg (fun value : Val m.value (.value out) =>
          rest.eval m entry (locals.snoc (.cons value .nil))) same.symm

theorem program_locals_eq {inputs : List (ValueSort Unit)} (rules : Rules m)
    (program : Program Op inputs out) (entry : Tuple (Val m.value) (dataPorts inputs)) :
    (fold rules program).dataflow.eval m entry PUnit.unit = program.dataflow.eval m entry PUnit.unit :=
  dataflow_eval (past := []) rules program.dataflow (entry := entry) (locals := PUnit.unit)
    (known := fun _ => none) (by intro t wire value impossible; cases impossible)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold
