module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Located
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Correctness

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Proofs

open RVSDG.Petri (Tokens)
open Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs (LocalFire)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args head outs : Ports (PortType V S)}
variable {past sigs : List (Ports (PortType V S))}

private theorem at_head_of_ret (m : Model.{u, v, w} Op) (node : Node Op args past head)
    (children : Children (Term Op) node) (wires : Wires args (past ++ [head]) outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {a b : Marking m (.bind node children (.ret wires))}
    (step : Fire m (.bind node children (.ret wires)) entry tokens a b) :
    LocalFire m node.kind children (RVSDG.Petri.read node.inputs entry tokens) a.1 b.1 := by
  cases step with
  | primitive ready ran => exact .primitive ready ran
  | enter ready choice => exact .enter ready choice
  | advance fired => exact .advance fired
  | commit ready choice => exact .commit ready choice
  | restart ready choice enters => exact .restart ready choice enters
  | later fired => cases fired

theorem consume_theta (m : Model.{u, v, w} Op)
    (body : Term Op head [] sigs (Theta.BodyResults head))
    (incoming : Wires args past head) (outgoing : Wires args (past ++ [head]) outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    (old : Tuple m.Val head) (child : Marking m body)
    (again : Bool) (next : Tuple m.Val head)
    (ready : finished m body old PUnit.unit child = some (Theta.bodyResult m again next))
    {after : Marking m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))}
    (step : Fire m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))
      entry tokens (.waiting (0 : Fin 1) (old, child), PUnit.unit) after) :
    after.1 = if again then .waiting (0 : Fin 1) (next, pending m body) else .done next := by
  have localStep := at_head_of_ret m _ _ outgoing entry tokens step
  change LocalFire m (.theta head) (fun _ => body) (RVSDG.Petri.read incoming entry tokens)
    (.waiting (0 : Fin 1) (old, child)) after.1 at localStep
  generalize same : after.1 = vertex at localStep ⊢
  clear same step after
  cases localStep with
  | advance fires =>
    exact False.elim (finished_no_step m body old PUnit.unit ready fires)
  | commit read decide =>
    have packetEq := Option.some.inj (ready.symm.trans read)
    rw [← packetEq] at decide
    cases again with
    | false => exact congrArg RVSDG.Petri.Vertex.done (Sum.inl.inj decide).symm
    | true => cases decide
  | restart read decide enters =>
    have packetEq := Option.some.inj (ready.symm.trans read)
    rw [← packetEq] at decide
    cases again with
    | false => cases decide
    | true =>
      have passed : next = _ := Sum.inr.inj decide
      have same := (congrArg Prod.snd (Option.some.inj enters)).symm
      exact congrArg (fun value =>
        (RVSDG.Petri.Vertex.waiting (0 : Fin 1) (value, pending m body) :
          RVSDG.Petri.Vertex (Tuple m.Val head) (fun _ : Fin 1 => Tuple m.Val head × Marking m body)))
        (same.trans passed.symm)

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Proofs
