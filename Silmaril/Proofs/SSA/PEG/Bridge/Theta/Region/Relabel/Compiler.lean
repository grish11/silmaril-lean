module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Defs
public import Silmaril.SSA.RVSDG.Theta.Institution.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Proofs

open RVSDG (Tuple Origin Wires)
open Simple.Revert.While.Region (Schedule Certificate)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Compiler
open RVSDG.Institution (mapTerm)

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {P Q : InstructionSet.{0,0} Data}
variable {carried vars outs : List (Ty Data)} {result : Ty Data} {n l : Nat}
variable {past : List (List (ValuePort Data))}
variable {g : Graph P carried [result] n 1} {allowInvariant : Bool}
variable (f : InstructionMap P Q)

private theorem refs_refl {s : Fin n → Ty Data} {ts : List (Ty Data)} (xs : Tuple (Ref s) ts) :
    xs.map (fun _ r => r.reindex (Equiv.refl _)) = xs := by
  induction xs with
  | nil => rfl
  | cons r _ ih => rw [Tuple.map, ih]; cases r; rfl

theorem mapOps_eq (graph : Graph P carried outs n l) :
    graph.mapOps f = table f graph := by
  have forest : graph.forest.reindex (Equiv.refl _) = graph.forest :=
    congrArg Graph.forest graph.mapOps_id
  simp only [Graph.mapOps, Graph.relabel, Node.relabel, Equiv.refl_symm, forest, table, node]
  exact congrArg₂ (fun (nodes : ∀ i, Node Q carried (Fin l) graph.sort (graph.sort i)) roots =>
    (⟨graph.forest, graph.sort, nodes, roots⟩ : Graph Q carried outs n l))
    (funext fun i => congrArg (Node.mk _ _) (refs_refl (graph.node i).args))
    (refs_refl graph.roots)

private def mapCode {outs : List (ValuePort Data)} (code : Code P carried past outs) :
    Code Q carried past outs :=
  ⟨code.1, mapTerm (opcode f) code.2⟩

private theorem slice_map {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    {results : List (ValuePort Data)} (code : Schedule g false roots scope) (layout : Scope carried vars past)
    (left : ∀ {past'}, Wires (valuePorts carried) past' (valuePorts outs) → Code P carried past' results)
    (right : ∀ {past'}, Wires (valuePorts carried) past' (valuePorts outs) → Code Q carried past' results)
    (aligned : ∀ past' (w : Wires (valuePorts carried) past' (valuePorts outs)), right w = mapCode f (left w)) :
    slice (schedule f code) layout right = mapCode f (slice code layout left) := by
  induction code generalizing past with
  | done reads => exact aligned _ (wires layout reads.slots)
  | bind i op refs fresh row reads tail ih =>
    simp only [schedule, slice, mapCode]
    rw [ih layout.push left right aligned]
    rfl
  | branch enabled => nomatch enabled

private theorem continue_map (cert : Certificate g allowInvariant) :
    continueArm (certificate f cert) = mapCode f (continueArm cert) :=
  slice_map f cert.update Scope.initial (fun w => ⟨[], .ret w⟩)
    (fun w => ⟨[], .ret w⟩) (fun _ _ => rfl)

private theorem select_map (cert : Certificate g allowInvariant)
    (flag : Origin (valuePorts carried) past (.value .bool))
    (old : Wires (valuePorts carried) past (valuePorts carried)) :
    select (certificate f cert) flag old = mapCode f (select cert flag old) := by
  have updates := continue_map f cert
  have arms :
      (Fin.cases (motive := fun i => RVSDG.Term (Opcode Q) (valuePorts carried) []
        ((selectNode cert old).childSigs i) (valuePorts carried))
        (.ret (args carried [])) (fun _ => mapTerm (opcode f) (continueArm cert).2)) =
        (fun i => mapTerm (opcode f) (selectArm cert old i)) := by
    funext i
    cases i using Fin.cases <;> rfl
  simp only [select, selectNode, selectArm, mapCode, mapTerm, branchNode, opcode]
  rw [updates]
  simp only [mapCode]
  rw [show _ = _ from arms]
  rfl

private theorem body_map (cert : Certificate g allowInvariant) :
    body (certificate f cert) = mapCode f (body cert) :=
  slice_map f cert.guard Scope.initial (guardFinish cert) (guardFinish (certificate f cert))
    (fun _ w => match w with | .cons flag old => select_map f cert flag old)

theorem compile_map (cert : Certificate g allowInvariant) :
    (⟨(body (certificate f cert)).1, compile (certificate f cert)⟩ :
      Σ sigs, RVSDG.Theta.Graph (Opcode Q) (valuePorts carried) sigs) =
    ⟨(body cert).1, RVSDG.Theta.Institution.relabel (opcode f) (compile cert)⟩ := by
  let collect (code : Code Q carried [] (RVSDG.Theta.BodyResults (valuePorts carried))) :
      Σ sigs, RVSDG.Theta.Graph (Opcode Q) (valuePorts carried) sigs :=
    ⟨code.1, (RVSDG.Theta.Term.mk code.2).toGraph⟩
  refine (congrArg collect (body_map f cert)).trans ?_
  unfold collect mapCode compile RVSDG.Theta.Institution.relabel RVSDG.Theta.Term.toGraph
  rw [RVSDG.Institution.mapGraph_toGraph]

end Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Proofs
