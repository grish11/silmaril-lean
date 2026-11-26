module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Checker
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Native

/-! Checked re-emission and partial observations at corresponding inputs. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open CategoryTheory
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (WordOp model word)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Model Val)
open Silmaril.SSA.SeaOfNodes.Diamond.Institution (reduct)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.Institution (Sentence mapGraph denote_mapGraph)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

universe w
variable {arity : Nat}

/-- The original checker transports successful plans and retains refusals. -/
theorem checkPlan_reindex (perm : InputPermutation arity) (spec : Spec) :
    checkPlan arity (spec.reindexInputs perm) =
      (checkPlan arity spec).map (fun p => p.reindexInputs perm) :=
  Proofs.Reindex.checkPlan_reindex perm spec

/-- Recheck the permuted spec and emit the RTL and λSSA of the typed map.
The RTL well-formedness gate succeeds after the permutation. -/
theorem lowerChecked_reindex {spec : Spec} {targets : Checked.Phi.Targets}
    (perm : InputPermutation arity) (accepted : lowerChecked arity spec = some targets) :
    ∃ p, checkPlan arity spec = some p ∧
      lowerChecked arity (spec.reindexInputs perm) =
        some (lowerBank (p.reindexInputs perm).graph, Generic.lower (p.reindexInputs perm).graph) :=
  Proofs.Reindex.lowerChecked_reindex perm accepted

theorem initial_reindex (p : Plan arity) (perm : InputPermutation arity)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (p.reindexInputs perm).graph.initial m input = p.graph.initial m (perm.pull input) :=
  Proofs.Reindex.initial_reindex p perm m input

theorem step_reindex (p : Plan arity) (perm : InputPermutation arity)
    (m : Model.{0, 0, w} WordOp) (input old : Tuple (Val m.value) (wordPorts arity)) :
    (p.reindexInputs perm).graph.step m input old = p.graph.step m (perm.pull input) old :=
  Proofs.Reindex.step_reindex m p perm input old

/-- The native input map preserves the entire partial observation at the
pulled valuation, in any total interpretation of the primitives. -/
theorem denote_reindex (p : Plan arity) (perm : InputPermutation arity)
    (m : Model.{0, 0, w} WordOp) (input : Tuple (Val m.value) (wordPorts arity)) :
    (p.reindexInputs perm).program.graph.denote m input =
      p.program.graph.denote m (perm.pull input) :=
  Proofs.Reindex.denote_reindex m p perm input

/-- Compose the input permutation with ordinary native opcode relabelling
and model reduct. The reduct uses the same valuation carriers. -/
theorem denote_mapGraph_reindex {Q : Silmaril.SSA.SeaOfNodes.Diamond.Institution.Signature.{0, 0} Unit}
    (h : wordSignature ⟶ Q)
    (p : Plan arity) (perm : InputPermutation arity) (m : Model.{0, 0, w} Q.op)
    (input : Tuple (Val m.value) (wordPorts arity)) :
    (mapGraph h (p.reindexInputs perm).program.graph).denote m input =
      p.program.graph.denote (reduct h m) (perm.pull input) :=
  (denote_mapGraph h m _ input).trans (denote_reindex p perm (reduct h m) input)

/-- Every old valuation is the pullback of its inverse-permuted valuation. -/
theorem InputPermutation.pull_symm {value : Unit → Type w} (perm : InputPermutation arity)
    (input : Tuple (Val value) (wordPorts arity)) :
    perm.pull (InputPermutation.pull perm.symm input) = input :=
  Proofs.Reindex.pull_symm perm input

/-- Permuting both interfaces preserves and reflects native equation satisfaction. -/
theorem equation_reindex_holds_iff (left right : Plan arity) (perm : InputPermutation arity)
    (m : Model.{0, 0, w} WordOp) :
    ((left.reindexInputs perm).equation (right.reindexInputs perm)).Holds m ↔
      (left.equation right).Holds m :=
  Proofs.Reindex.equation_reindex_holds_iff m left right perm

/-- The native equation can also be relabelled along an opcode signature map. -/
theorem equation_reindex_map_holds_iff
    {Q : Silmaril.SSA.SeaOfNodes.Diamond.Institution.Signature.{0, 0} Unit}
    (h : wordSignature ⟶ Q) (left right : Plan arity) (perm : InputPermutation arity)
    (m : Model.{0, 0, w} Q.op) :
    ((Sentence.equation ((left.reindexInputs perm).equation (right.reindexInputs perm))).map h).Holds m ↔
      (left.equation right).Holds (reduct h m) :=
  (Sentence.satisfaction h (.equation ((left.reindexInputs perm).equation (right.reindexInputs perm))) m).trans
    (equation_reindex_holds_iff left right perm (reduct h m))

variable {p : Plan arity} {spec : Spec} {targets : Checked.Phi.Targets}

private theorem rechecked (perm : InputPermutation arity) (checked : checkPlan arity spec = some p) :
    checkPlan arity (spec.reindexInputs perm) = some (p.reindexInputs perm) := by
  rw [checkPlan_reindex, checked]
  rfl

theorem rtl_reindex_return_iff (perm : InputPermutation arity)
    (checked : checkPlan arity spec = some p)
    (emitted : lowerChecked arity (spec.reindexInputs perm) = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, value ∈ p.program.graph.denote model (perm.pull input) ∧
        returned = [value] ∧ final = initial := by
  rw [rtl_return_iff (rechecked perm checked) emitted, denote_reindex]
  rfl

theorem lambda_reindex_return_iff (perm : InputPermutation arity)
    (checked : checkPlan arity spec = some p)
    (emitted : lowerChecked arity (spec.reindexInputs perm) = some targets) (input : WordTuple arity)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value : Word, value ∈ p.program.graph.denote model (perm.pull input) ∧
        label = 0 ∧ payload = Generic.packResult model (out := word) value ∧ final = initial := by
  rw [lambda_return_iff (rechecked perm checked) emitted, denote_reindex]
  rfl

/-- Undefinedness at the pulled native valuation means no finite return
from either re-emitted target, independent of any runner budget. -/
theorem reindex_no_finite_return_iff (perm : InputPermutation arity)
    (checked : checkPlan arity spec = some p)
    (emitted : lowerChecked arity (spec.reindexInputs perm) = some targets)
    (input : WordTuple arity) (initial : Memory) :
    ((∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
        p.program.graph.denote model (perm.pull input) = Part.none) ∧
    ((∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
        targets.2 initial label payload final) ↔
        p.program.graph.denote model (perm.pull input) = Part.none) := by
  simpa only [denote_reindex] using no_finite_return_iff (rechecked perm checked) emitted input initial

section Equation

variable {left right : Plan arity} {leftSpec rightSpec : Spec}
variable {leftTargets rightTargets : Checked.Phi.Targets}

/-- Compare the re-emitted targets at a new valuation using the original
native equation at its pullback. Both observations include the entire memory. -/
theorem reindex_equation_at_iff (perm : InputPermutation arity)
    (leftPlan : checkPlan arity leftSpec = some left) (rightPlan : checkPlan arity rightSpec = some right)
    (leftLower : lowerChecked arity (leftSpec.reindexInputs perm) = some leftTargets)
    (rightLower : lowerChecked arity (rightSpec.reindexInputs perm) = some rightTargets)
    (input : WordTuple arity) (initial : Memory) :
    rtlObservation leftTargets.1 input initial = lambdaObservation rightTargets.2 input initial ↔
      left.program.graph.denote model (perm.pull input) = right.program.graph.denote model (perm.pull input) := by
  rw [equation_at_iff (rechecked perm leftPlan) (rechecked perm rightPlan) leftLower rightLower]
  simp only [denote_reindex]

/-- Equality of the re-emitted target observations at all new valuations
is equivalent to satisfaction of the original native equation. -/
theorem reindex_equation_holds_iff (perm : InputPermutation arity)
    (leftPlan : checkPlan arity leftSpec = some left) (rightPlan : checkPlan arity rightSpec = some right)
    (leftLower : lowerChecked arity (leftSpec.reindexInputs perm) = some leftTargets)
    (rightLower : lowerChecked arity (rightSpec.reindexInputs perm) = some rightTargets)
    (initial : Memory) :
    (left.equation right).Holds model ↔
      ∀ input : WordTuple arity,
        rtlObservation leftTargets.1 input initial = lambdaObservation rightTargets.2 input initial :=
  (equation_reindex_holds_iff left right perm model).symm.trans
    (equation_holds_iff (rechecked perm leftPlan) (rechecked perm rightPlan) leftLower rightLower initial)

end Equation

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
