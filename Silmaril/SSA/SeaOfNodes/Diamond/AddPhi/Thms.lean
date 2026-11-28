module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi

open Pure.ConstantFold (Literals)
open Pure.SubZero (model)
open RVSDG (Locals Tuple)

/-- The explicit literal scan agrees with the interpreted table under any sound initial facts. -/
theorem scanLiterals_agrees {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
    (flow : Dataflow Pure.SubZero.Opcode args past sigs) (known : Literals args past)
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past)
    (agree : Pure.ConstantFold.Scan.Literals.Agrees known entry locals) :
    Pure.ConstantFold.Scan.Literals.Agrees (scanLiterals known flow) entry (flow.eval model entry locals) :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.scan_agrees flow known entry locals agree

/-- The emitted literal arm returns just its folded word. -/
theorem literalArm_eval {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) (value : BitVec 64) :
    (literalArm value).eval model entry locals = .cons value .nil :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.literalArm_eval entry locals value

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : WordGraph inputs sigs} {rhs : WordWire inputs sigs} {target : Result inputs sigs}

/-- Successful rewrites keep the shared table, predicate and Region predecessors. -/
theorem rewrite?_keeps_control (accepted : rewrite? g rhs = some target) :
    target.shared = g.dataflow ∧ target.predicate = g.predicate ∧ target.merge = g.phi.merge :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.keeps_control accepted

/-- Each output arm implements the add at the same original predecessor occurrence. -/
theorem rewrite?_slot_eval_eq (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (target.arms slot).eval model entry (target.shared.eval model entry PUnit.unit) =
      .cons (sourceAt g rhs entry slot) .nil :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.slot_eval_eq accepted entry slot

/-- For every typed input, the taken predecessor returns the original modular sum. -/
theorem rewrite?_denote_eq (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote model entry = .cons (sourceDenote g rhs entry) .nil :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.denote_eq accepted entry

/-- The emitted native Diamond preserves and reflects the scoped finite return. -/
theorem rewrite?_returns_iff (accepted : rewrite? g rhs = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (result : BitVec 64) :
    target.Returns model entry (.cons result .nil) ↔ SourceReturns g rhs entry result :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.returns_iff accepted entry result

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi
