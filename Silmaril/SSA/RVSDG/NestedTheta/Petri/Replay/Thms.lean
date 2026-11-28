module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Replay.Completeness
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Replay.Theta

/-! The firing checker recognizes the original relation. The phase laws
focus a θ whose continuation returns immediately. -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay

open RVSDG.Petri (Tokens)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

theorem checkFire_complete (m : Model.{u, v, w} Op) (colourEq : (t : PortType V S) → DecidableEq (m.Val t))
    {term : Term Op args past sigs outs} {entry : Tuple m.Val args} {tokens : Tokens m.Val past}
    {before after : Marking m term} (step : Fire m term entry tokens before after) :
    (checkFire m colourEq term entry tokens before after).isSome :=
  Proofs.checkFire_complete m colourEq step

theorem pending_theta (m : Model.{u, v, w} Op)
    (body : Term Op head [] sigs (Theta.BodyResults head))
    (incoming : Wires args past head) (outgoing : Wires args (past ++ [head]) outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {after : Marking m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))}
    (step : Fire m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))
      entry tokens (.pending, PUnit.unit) after) :
    ∃ bank, RVSDG.Petri.read incoming entry tokens = some bank ∧
      after = (.waiting (0 : Fin 1) (bank, pending m body), PUnit.unit) :=
  Proofs.pending_theta m body incoming outgoing entry tokens step

theorem unfinished_theta (m : Model.{u, v, w} Op)
    (body : Term Op head [] sigs (Theta.BodyResults head))
    (incoming : Wires args past head) (outgoing : Wires args (past ++ [head]) outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (old : Tuple m.Val head) (child : Marking m body)
    (unfinished : finished m body old PUnit.unit child = none)
    {after : Marking m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))}
    (step : Fire m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))
      entry tokens (.waiting (0 : Fin 1) (old, child), PUnit.unit) after) :
    ∃ next, Fire m body old PUnit.unit child next ∧
      after = (.waiting (0 : Fin 1) (old, next), PUnit.unit) :=
  Proofs.unfinished_theta m body incoming outgoing entry tokens old child unfinished step

theorem committed_theta (m : Model.{u, v, w} Op)
    (body : Term Op head [] sigs (Theta.BodyResults head))
    (incoming : Wires args past head) (outgoing : Wires args (past ++ [head]) outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (result : Tuple m.Val head)
    {after : Marking m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))}
    (step : Fire m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))
      entry tokens (.done result, PUnit.unit) after) : False :=
  Proofs.committed_theta m body incoming outgoing entry tokens result step

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay
