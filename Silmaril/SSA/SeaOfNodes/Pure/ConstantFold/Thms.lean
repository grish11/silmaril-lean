module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open SubZero (model)
open RVSDG (Locals Tuple Wires)

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}

namespace Scan

variable {Op : Signature Unit} {m : Model Op}

/-- Extending the producer store preserves earlier facts and records any
sound fact for the new result. -/
theorem Literals.push_agrees {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    {known : Literals m args past} {entry : Tuple (Val m.value) args}
    {locals : Locals (Val m.value) past} (agree : known.Agrees entry locals)
    {actual : Val m.value (.value out)} {hint : Option (Val m.value (.value out))}
    (sound : ∀ value, hint = some value → actual = value) :
    Literals.Agrees (known.push hint) entry (locals.snoc (.cons actual .nil)) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.push_agrees agree sound

/-- Any literal predicted by the existing rule has the binding's value. -/
theorem Rule.replacement_sound {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    {known : Literals m args past} {entry : Tuple (Val m.value) args}
    {locals : Locals (Val m.value) past} (agree : known.Agrees entry locals)
    {ins : List (ValueSort Unit)} {op : Op ins out} (rule : Rule m op)
    (operands : Wires args past (dataPorts ins)) {literal : Op [] out}
    (found : rule.replacement? known operands = some literal) :
    m.run op (operands.read entry locals) = m.run literal .nil :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.replacement_sound agree rule operands found

/-- The literal facts also agree when the original binding is retained. -/
theorem Rule.record_agrees {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    {known : Literals m args past} {entry : Tuple (Val m.value) args}
    {locals : Locals (Val m.value) past} (agree : known.Agrees entry locals)
    {ins : List (ValueSort Unit)} {op : Op ins out} (rule : Rule m op)
    (operands : Wires args past (dataPorts ins)) :
    Literals.Agrees (rule.record known operands) entry
      (locals.snoc (.cons (m.run op (operands.read entry locals)) .nil)) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.record_agrees agree rule operands

/-- The certified scan preserves all final producer slots at every input. -/
theorem fold_locals_eq (rules : Rules m) (program : Program Op inputs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) :
    (fold rules program).dataflow.eval m entry PUnit.unit = program.dataflow.eval m entry PUnit.unit :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.program_locals_eq rules program entry

/-- The certified scan preserves the typed return. -/
theorem fold_eval_eq (rules : Rules m) (program : Program Op inputs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) :
    (fold rules program).eval m entry = program.eval m entry :=
  congrArg (Diamond.read m program.result entry) (fold_locals_eq rules program entry)

end Scan

/-- Folding retains the exact result-port signatures. -/
theorem fold_sigs (program : Program SubZero.Opcode inputs out) :
    (fold program).sigs = program.sigs := rfl

/-- Every final producer slot contains the same typed value. -/
theorem fold_locals_eq (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (fold program).dataflow.eval model entry PUnit.unit = program.dataflow.eval model entry PUnit.unit :=
  Scan.fold_locals_eq arithmeticRules program entry

/-- The native return is unchanged at every typed input. -/
theorem fold_eval_eq (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (fold program).eval model entry = program.eval model entry :=
  congrArg (Diamond.read model program.result entry) (fold_locals_eq program entry)

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
