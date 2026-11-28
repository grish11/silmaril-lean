module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Correctness
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Theta
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Cut.Correctness

/-! Invert actual firings at a typed observation cut. -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

open RVSDG.Petri (Tokens)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args bank outs : Ports (PortType V S)}
variable {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}
variable {front : Term Op args past frontSigs bank} {whole : Term Op args past wholeSigs outs}
variable {tail : Term Op args (extend past frontSigs) tailSigs outs}
variable (cut : Cut front whole tail) (m : Model.{u, v, w} Op)

theorem Cut.rest_attach (mark : Marking m front) (rest : Marking m tail) :
    cut.rest m (cut.attach m mark rest) = rest :=
  Cut.Proofs.rest_attach cut m mark rest

theorem Cut.attach_observe_rest (mark : Marking m whole) :
    cut.attach m (cut.observe m mark) (cut.rest m mark) = mark :=
  Cut.Proofs.attach_observe_rest cut m mark

theorem Cut.observe_pending : cut.observe m (pending m whole) = pending m front :=
  Cut.Proofs.observe_pending cut m

theorem Cut.lift_tail_step (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (mark : Marking m front)
    {before after : Marking m tail}
    (step : Fire m tail entry (cut.tokens m tokens mark) before after) :
    Fire m whole entry tokens (cut.attach m mark before) (cut.attach m mark after) :=
  Cut.Proofs.tail_step cut m entry tokens mark step

/-- A legal firing occurs before the cut or in its continuation. On the
other side, the exact marking stays fixed. -/
theorem Cut.split_step (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {before after : Marking m whole} (step : Fire m whole entry tokens before after) :
    (Fire m front entry tokens (cut.observe m before) (cut.observe m after) ∧
      cut.rest m before = cut.rest m after) ∨
    (cut.observe m before = cut.observe m after ∧
      Fire m tail entry (cut.tokens m tokens (cut.observe m before)) (cut.rest m before) (cut.rest m after)) :=
  Cut.Proofs.split_step cut m entry tokens step

theorem Cut.observe_reaches (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {before after : Marking m whole} (steps : ReflTransGen (Fire m whole entry tokens) before after) :
    ReflTransGen (Fire m front entry tokens) (cut.observe m before) (cut.observe m after) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih =>
    rcases cut.split_step m entry tokens step with ⟨fire, _⟩ | ⟨same, _⟩
    · exact ih.tail fire
    · exact same ▸ ih

/-- In a completed region, the original prefix also has all of its
results marked. Root entry arguments are already present. -/
theorem Cut.completed_prefix
    {front : Term Op args [] frontSigs bank} {whole : Term Op args [] wholeSigs outs}
    {tail : Term Op args (extend [] frontSigs) tailSigs outs} (cut : Cut front whole tail)
    (entry : Tuple m.Val args) (mark : Marking m whole) {output : Tuple m.Val outs}
    (done : finished m whole entry PUnit.unit mark = some output) :
    ∃ result, finished m front entry PUnit.unit (cut.observe m mark) = some result :=
  Cut.Proofs.completed_prefix cut m entry mark done

theorem finished_no_step (term : Term Op args past wholeSigs outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past) {before after : Marking m term}
    {output : Tuple m.Val outs} (done : finished m term entry tokens before = some output)
    (step : Fire m term entry tokens before after) : False :=
  Proofs.finished_no_step m term entry tokens done step

/-- With a return continuation, a completed live θ body can only restart or commit the binder. -/
theorem consume_theta
    {head : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}
    (body : Term Op head [] sigs (Theta.BodyResults head))
    (incoming : Wires args past head) (outgoing : Wires args (past ++ [head]) outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    (old : Tuple m.Val head) (child : Marking m body)
    (again : Bool) (next : Tuple m.Val head)
    (ready : finished m body old PUnit.unit child = some (Theta.bodyResult m again next))
    {after : Marking m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))}
    (step : Fire m (.bind ⟨head, .theta head, incoming, fun _ => sigs⟩ (fun _ => body) (.ret outgoing))
      entry tokens (.waiting (0 : Fin 1) (old, child), PUnit.unit) after) :
    after.1 = if again then .waiting (0 : Fin 1) (next, pending m body) else .done next :=
  Proofs.consume_theta m body incoming outgoing entry tokens old child again next ready step

end Silmaril.SSA.RVSDG.NestedTheta.Petri
