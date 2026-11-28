module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.ZeroSample
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Append
import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {s : State P params results n l} {g : Graph P params results n l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable {site : Fin n} {zero : P [] .count}

theorem zeroSample_holds (found : ZeroSample g site zero)
    (law : m.run zero .nil = some ⟨0⟩) {values : found.row.append.Valuation m}
    (solves : found.row.append.Solves m env values) : found.equation.Holds values := by
  intro _
  let row := found.row
  have countZero (idx : Index l) : Rules.readRef values (row.liftRef found.count) idx = some ⟨0⟩ :=
    (Rules.at_label solves (lift_hasNode row found.countNode) idx).trans law
  exact (Rules.streamEq_iff_vertex (g := row.append) (values := values)
    (row.liftRef (Ref.ofId g.sort site)) row.fresh).mp
    (Rules.eval_zero_theta solves (lift_hasNode row found.evalNode)
      (lift_hasNode row found.thetaNode) (node_fresh row) countZero)

theorem zeroSample_step_holds (found : ZeroSample s.graph site zero)
    (law : m.run zero .nil = some ⟨0⟩) : found.step.Holds env := by
  intro values solves reason member
  have same : reason = .guarded found.equation := List.mem_singleton.mp member
  subst reason
  exact zeroSample_holds found law solves

theorem zeroSample_equates (found : ZeroSample s.graph site zero) :
    found.step.apply.classes site.castSucc = found.step.apply.classes (Fin.last n) := by
  let reason : Saturation.Obligation found.row.append := .guarded found.equation
  exact Saturation.saturate_closed [reason] (Row.liftClasses s.classes) reason (by simp) rfl

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension
