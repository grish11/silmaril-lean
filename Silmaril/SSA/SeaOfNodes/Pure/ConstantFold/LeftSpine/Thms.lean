module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine

open Diamond (Ty Val ValueSort dataPorts)
open GVN (weaken)
open GVN.Elimination (Rewrite Routing)
open RightSpine (Prefix WordWire)
open SubZero (model)
open RVSDG (Tuple)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {ids : SourceIds} {known : Prefix args past} {lhs rhs : WordWire args past}

/-- Extending the scan prefix preserves the source-ID lookup of an old wire. -/
theorem SourceIds.atWire_weaken (ids : SourceIds) (head : List (Ty Unit)) (wire : WordWire args past) :
    ids.atWire (weaken head wire) = ids.atWire wire :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.atWire_weaken ids head wire

/-- With supplied source IDs this is the pinned comparison after removing
the Φ cases. The right literal test takes priority over the left one. -/
theorem compare_of_ids {literals : Literals args past} {hi lo : WordWire args past} {hiId loId : Int32}
    (hiSource : ids.atWire hi = some hiId) (loSource : ids.atWire lo = some loId) :
    compare? ids literals hi lo =
      some (if (literals lo).isSome then false else if (literals hi).isSome then true else decide (hiId < loId)) := by
  by_cases loLiteral : (literals lo).isSome <;> by_cases hiLiteral : (literals hi).isSome <;>
    simp [compare?, loLiteral, hiLiteral, hiSource, loSource]

/-- Two nonliterals pass precisely when both source IDs exist in the
required strict order. -/
theorem compare_nonliteral_iff {literals : Literals args past} {hi lo : WordWire args past}
    (hiUnknown : literals hi = none) (loUnknown : literals lo = none) :
    compare? ids literals hi lo = some true ↔
      ∃ hiId loId, ids.atWire hi = some hiId ∧ ids.atWire lo = some loId ∧ hiId < loId := by
  cases hiSource : ids.atWire hi <;> cases loSource : ids.atWire lo <;>
    simp [compare?, hiUnknown, loUnknown, hiSource, loSource]

/-- An accepted edit passes the preceding shape and literal checks and
uses the actual ordered left addends and outer right wire. -/
theorem match_exact {edit : AddRewrite.Splice args past} (accepted : matchAdd? ids known lhs rhs = some edit) :
    (known.literals lhs).isNone = true ∧ (known.literals rhs).isNone = true ∧
      lhs.address ≠ rhs.address ∧ (known.addends rhs).isNone = true ∧
      ∃ left, known.addends lhs = some left ∧ compare? ids known.literals left.right rhs = some true ∧
        edit = permute left rhs :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.match_exact accepted

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

/-- Every original typed read agrees along the returned routing. -/
theorem step_agrees (accepted : step? ids program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.step_agrees accepted entry

/-- The routed return agrees for every input under wrapping word addition. -/
theorem step_eval_eq (accepted : step? ids program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (AddRewrite.rewrittenProgram program rewrite).eval model entry = program.eval model entry :=
  (step_agrees accepted entry _ program.result).symm

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine
