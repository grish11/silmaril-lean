module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Correct
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Synthesis.Transfer

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family

open NestedTheta.Liveness
open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {shape : MemberSummaries V S} {imports : Ports (Ty V S)}
variable {calls : CallTransfer shape} {past : List (Ports (Ty V S))}
variable (template : Template Op shape imports calls past)

/-- Increasing candidate summaries can only increase the next round. -/
theorem Template.round_monotone : Monotone template.round := Proofs.round_mono template

/-- A stable result is reached within the finite input-bit budget. -/
theorem Template.synthesize_fixed : template.round template.synthesize = template.synthesize :=
  Proofs.synthesize_fixed template

/-- Every overapproximation closed under the joint transfer bounds the result. -/
theorem Template.synthesize_le {upper : Rows shape} (closed : template.round upper ≤ upper) :
    template.synthesize ≤ upper := Proofs.synthesize_le template closed

theorem Template.synthesize_isLeast : IsLeast {rows | template.round rows ≤ rows} template.synthesize :=
  ⟨(template.synthesize_fixed).le, fun _ h => template.synthesize_le h⟩

/-- Compare directly against a supplied transfer closed at every finite
row. The inferred summary is included even when queried with a raw demand. -/
theorem Template.synthesize_le_supplied (reads : MemberTransfer shape.members.length)
    (closed : step template reads ≤ rowsOfTransfer (shape := shape) reads) :
    ∀ i demand, template.summaries.live i demand ⊆ reads.live i demand :=
  Proofs.synthesize_le_supplied template reads closed

/-- At the fixed point lookup reads the exact row for the requested positions. -/
theorem Template.synthesize_read (i : Fin shape.members.length) (demand : Demand) :
    readRow shape template.synthesize i demand = row shape template.synthesize i (demandMask demand) :=
  Proofs.synthesize_read template i demand

/-- The projected result covers every actual body read at each demand. -/
theorem Template.synthesize_closed (safe : template.ReferenceSafe) (i : Fin shape.members.length)
    (demand : Demand) :
    let live := (((template.body i).withTransfer template.callReads).plan demand).live
    (∀ p, p < (memberPorts shape.members).length → .arg p ∉ live) ∧
    ∀ p, .arg ((memberPorts shape.members).length + p) ∈ live → .arg p ∈ template.summaries.live i demand :=
  Proofs.synthesized_closed template safe i demand

/-- Certify closure for all demands. Checking the full output demand suffices
to exclude reads of the reference prefix. Actual target and capture witnesses
are still checked by the linked family's `Ready` or `ReadyWith` condition. -/
@[expose] def Template.admit (safe : template.ReferenceSafe) :
    StaticDemand.Family Op template.summaries imports
      (calls.signatures.withReads template.callReads) past where
  context := template.context
  captures := template.captures
  memberWires := template.memberWires
  sigs := template.sigs
  body i := (template.body i).withTransfer template.callReads
  closed := template.synthesize_closed safe

/-- The inferred summary changes only the demand interpretation of a member. -/
theorem Template.admit_term (safe : template.ReferenceSafe) (i : Fin shape.members.length) :
    ((template.admit safe).body i).term = (template.body i).term :=
  Proofs.transfer_term (template.body i) template.callReads

variable (template : Template Op shape imports)

variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}

/-- Instantiate the actual linked partial runner's transport with the inferred
summary. It preserves the typed endpoints and observations after resumption
at arbitrary finite budgets. -/
theorem Template.linked_prefixes_agree (safe : template.ReferenceSafe) (i : Fin shape.members.length)
    (actions : Actions m σ) (demand : Demand) (fuel after unitId : Nat)
    (importedL importedR : Tuple m.Val imports)
    (argsL argsR : Tuple m.Val (shape.at i).fn.args) (store : σ)
    (readyL : (template.admit safe).Ready (template.captures.read importedL PUnit.unit))
    (readyR : (template.admit safe).Ready (template.captures.read importedR PUnit.unit))
    (agree : (template.admit safe).AgreesOnInputs i demand importedL importedR argsL argsR) :
    ∃ left right,
      (template.admit safe).run i actions fuel unitId importedL argsL store = .ok left ∧
      (template.admit safe).run i actions fuel unitId importedR argsR store = .ok right ∧
      PrefixObservationsAgree actions demand after left right :=
  (template.admit safe).linked_prefixes_agree i actions demand fuel after unitId importedL importedR argsL argsR
    store readyL readyR agree

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family
