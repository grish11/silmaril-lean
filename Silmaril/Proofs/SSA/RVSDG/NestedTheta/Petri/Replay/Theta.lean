module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Located

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Proofs

open RVSDG.Petri (Tokens read)
open Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs (LocalFire)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args head outs : Ports (PortType V S)}
variable {past sigs : List (Ports (PortType V S))}
variable (m : Model.{u, v, w} Op)

private theorem local_of_ret (node : Node Op args past head)
    (children : Children (Term Op) node) (wires : Wires args (past ++ [head]) outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {before after : Marking m (.bind node children (.ret wires))}
    (step : Fire m (.bind node children (.ret wires)) entry tokens before after) :
    LocalFire m node.kind children (RVSDG.Petri.read node.inputs entry tokens) before.1 after.1 := by
  cases step with
  | primitive ready ran => exact .primitive ready ran
  | enter ready picked => exact .enter ready picked
  | advance step => exact .advance step
  | commit ready picked => exact .commit ready picked
  | restart ready picked fork => exact .restart ready picked fork
  | later step => cases step

variable (body : Term Op head [] sigs (Theta.BodyResults head))
variable (incoming : Wires args past head) (outgoing : Wires args (past ++ [head]) outs)
variable (entry : Tuple m.Val args) (tokens : Tokens m.Val past)

theorem pending_theta
    {after : Marking m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))}
    (step : Fire m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))
      entry tokens (.pending, PUnit.unit) after) :
    ∃ bank, RVSDG.Petri.read incoming entry tokens = some bank ∧
      after = (.waiting (0 : Fin 1) (bank, pending m body), PUnit.unit) := by
  have located := local_of_ret m _ _ outgoing entry tokens step
  change LocalFire m (.theta head) (fun _ => body) (RVSDG.Petri.read incoming entry tokens)
    .pending after.1 at located
  have facts : ∃ bank, RVSDG.Petri.read incoming entry tokens = some bank ∧
      after.1 = .waiting (0 : Fin 1) (bank, pending m body) := by
    generalize same : after.1 = vertex at located ⊢
    clear same step after
    cases located with
    | primitive _ ready => cases ready
    | enter ready guard =>
      cases Option.some.inj guard
      exact ⟨_, ready, rfl⟩
  obtain ⟨bank, ready, phase⟩ := facts
  exact ⟨bank, ready, Prod.ext phase (Subsingleton.elim (α := PUnit) _ _)⟩

theorem unfinished_theta (old : Tuple m.Val head) (child : Marking m body)
    (unfinished : finished m body old PUnit.unit child = none)
    {after : Marking m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))}
    (step : Fire m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))
      entry tokens (.waiting (0 : Fin 1) (old, child), PUnit.unit) after) :
    ∃ next, Fire m body old PUnit.unit child next ∧
      after = (.waiting (0 : Fin 1) (old, next), PUnit.unit) := by
  have located := local_of_ret m _ _ outgoing entry tokens step
  change LocalFire m (.theta head) (fun _ => body) (RVSDG.Petri.read incoming entry tokens)
    (.waiting (0 : Fin 1) (old, child)) after.1 at located
  have facts : ∃ next, Fire m body old PUnit.unit child next ∧
      after.1 = .waiting (0 : Fin 1) (old, next) := by
    generalize same : after.1 = vertex at located ⊢
    clear same step after
    cases located with
    | advance step => exact ⟨_, step, rfl⟩
    | commit ready _ | restart ready _ _ => cases unfinished.symm.trans ready
  obtain ⟨bank, ready, phase⟩ := facts
  exact ⟨bank, ready, Prod.ext phase (Subsingleton.elim (α := PUnit) _ _)⟩

theorem committed_theta (result : Tuple m.Val head)
    {after : Marking m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))}
    (step : Fire m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))
      entry tokens (.done result, PUnit.unit) after) : False := by
  have located := local_of_ret m _ _ outgoing entry tokens step
  change LocalFire m (.theta head) (fun _ => body) (RVSDG.Petri.read incoming entry tokens)
    (.done result) after.1 at located
  generalize same : after.1 = vertex at located
  clear same step after
  cases located

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Proofs
