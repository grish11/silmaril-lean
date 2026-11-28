module

public import Silmaril.SSA.Peggy.Worked.StrengthReduction.Defs
import Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction.Recurrence
import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.Worked.StrengthReduction
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat} {g : Graph P params results n l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable {site : Fin n} {ops : Profile P}

theorem target_theta (found : Match g site ops) :
    Rules.HasNode (g := found.candidate) found.resultRef (.theta found.loop) found.thetaArgs := by
  let replacement : Node P params (Fin l) found.added.sort .count :=
    Node.ofLabel (.theta found.loop) found.thetaArgs
  have chosen : found.candidate.node found.resultRef.id =
      (found.resultRef.typed.symm ▸ replacement :
        Node P params (Fin l) found.added.sort (found.added.sort found.resultRef.id)) :=
    dite_eq_left (show found.resultRef.id = found.resultRef.id from rfl)
  exact (heq_of_eq chosen).trans (eqRec_heq found.resultRef.typed.symm replacement)

theorem target_other (found : Match g site ops) (i : Fin (n + 1)) (different : found.resultRef.id ≠ i) :
    found.candidate.node i = found.added.append.node i :=
  dite_eq_right different

private theorem use_equation {t : Ty Data} {inputs : List (Ty Data)}
    (values : g.Valuation m) (r : Ref g.sort t) (label : Label P params (Fin l) inputs t)
    (args : Tuple (Ref g.sort) inputs) (shape : Rules.HasNode r label args) (idx : Index l) :
    r.read m.carrier (g.equation m env values (r.id, idx)) =
      label.interpret m env idx (fun slot j _ => Rules.readRef values (args.get (portAt inputs slot)) j) := by
  obtain ⟨id, eq⟩ := r
  subst t
  have node : g.node id = Node.ofLabel label args := eq_of_heq shape
  change (g.node id).label.interpret m env idx
    (fun slot j _ => Rules.readRef values ((g.node id).arg slot) j) = _
  rw [node]
  rfl

private theorem read_injective {t : Ty Data} (r : Ref g.sort t) :
    Function.Injective (r.read m.carrier) := by
  obtain ⟨id, eq⟩ := r
  subst t
  exact fun _ _ h => h

theorem lifted_solution (found : Match g site ops) (law : Law m ops)
    {vals : found.added.append.Valuation m}
    (solves : found.added.append.Solves m env vals) : found.candidate.Solves m env vals := by
  rintro ⟨id, idx⟩
  by_cases changeRow : found.resultRef.id = id
  · subst id
    apply read_injective (g := found.candidate) (m := m) found.resultRef
    change Rules.readRef vals found.resultRef idx =
      found.resultRef.read m.carrier (found.candidate.equation m env vals (found.resultRef.id, idx))
    have unfolded := use_equation (g := found.candidate) (env := env) vals found.resultRef
      _ _ (target_theta found) idx
    have thetaStep := Rules.interpret_theta m env idx found.loop (out := .count)
      (fun slot j => Rules.readRef (g := found.candidate) vals
        (found.thetaArgs.get (portAt [.count, .count] slot)) j)
    have eq := scaled_recurrence solves law (found.added.lift_hasNode found.scaleNode)
      (found.added.lift_hasNode found.factorNode) (found.added.lift_hasNode found.thetaNode)
      (found.added.lift_hasNode found.baseNode) (found.added.lift_hasNode found.stepNode)
      found.added.node_fresh idx
    exact eq.trans (thetaStep.symm.trans unfolded.symm)
  · let row := found.added.append.node id
    let ref := Ref.ofId found.added.sort id
    have oldShape : Rules.HasNode (g := found.added.append) ref row.label row.args := by
      change HEq row (Node.ofLabel row.label row.args)
      cases row
      rfl
    have newShape : Rules.HasNode (g := found.candidate) ref row.label row.args := by
      exact (heq_of_eq (target_other found id changeRow)).trans oldShape
    exact (solves (id, idx)).trans
      ((use_equation (g := found.added.append) vals ref row.label row.args oldShape idx).trans
        (use_equation (g := found.candidate) vals ref row.label row.args newShape idx).symm)

theorem rewrite_sound (found : Match g site ops) (law : Law m ops)
    (before : WellFounded g.Demand) (after : WellFounded found.candidate.Demand) (idx : Index l) :
    g.observe m (g.denote m env before) idx =
      found.candidate.observe m (found.candidate.denote m env after) idx := by
  let appendWF := found.added.demandWellFounded before
  let vals := found.added.append.denote m env appendWF
  have same : vals = found.candidate.denote m env after :=
    found.candidate.solves_unique m env after
      (lifted_solution found law (found.added.append.denote_solves m env appendWF))
      (found.candidate.denote_solves m env after)
  calc
    _ = found.added.append.observe m vals idx := (found.added.observe_eq before appendWF idx).symm
    _ = _ := congrArg (fun values => found.candidate.observe m values idx) same

end Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction
