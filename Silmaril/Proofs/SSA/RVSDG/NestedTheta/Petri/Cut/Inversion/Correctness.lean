module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Defs
import Silmaril.Proofs.SSA.RVSDG.Petri.Colours

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Proofs

open RVSDG.Petri (Tokens)
open RVSDG.Petri.Proofs (full full_snoc read_full)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args bank outs : Ports (PortType V S)}
variable {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}
variable {front : Term Op args past frontSigs bank} {whole : Term Op args past wholeSigs outs}
variable {tail : Term Op args (extend past frontSigs) tailSigs outs}
variable (cut : Cut front whole tail) (m : Model.{u, v, w} Op)

theorem rest_attach (mark : Marking m front) (rest : Marking m tail) :
    cut.rest m (cut.attach m mark rest) = rest := by
  induction cut with
  | stop => rfl
  | bind _ _ _ ih => exact ih mark.2 rest

theorem attach_observe_rest (mark : Marking m whole) :
    cut.attach m (cut.observe m mark) (cut.rest m mark) = mark := by
  induction cut with
  | stop => rfl
  | bind _ _ _ ih => exact congrArg (Prod.mk mark.1) (ih mark.2)

theorem observe_pending : cut.observe m (pending m whole) = pending m front := by
  induction cut with
  | stop => rfl
  | bind _ _ _ ih => exact congrArg (fun mark => (_, mark)) ih

theorem split_step (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    {before after : Marking m whole} (step : Fire m whole entry tokens before after) :
    (Fire m front entry tokens (cut.observe m before) (cut.observe m after) ∧
      cut.rest m before = cut.rest m after) ∨
    (cut.observe m before = cut.observe m after ∧
      Fire m tail entry (cut.tokens m tokens (cut.observe m before)) (cut.rest m before) (cut.rest m after)) := by
  induction cut with
  | stop => exact .inr ⟨rfl, step⟩
  | bind _ _ _ ih =>
    cases step with
    | primitive ready result => exact .inl ⟨.primitive ready result, rfl⟩
    | enter ready picked => exact .inl ⟨.enter ready picked, rfl⟩
    | advance firing => exact .inl ⟨.advance firing, rfl⟩
    | commit ready route => exact .inl ⟨.commit ready route, rfl⟩
    | restart ready route picked => exact .inl ⟨.restart ready route picked, rfl⟩
    | later firing =>
      rcases ih _ firing with ⟨front, same⟩ | ⟨same, tail⟩
      · exact .inl ⟨.later front, same⟩
      · exact .inr ⟨congrArg (fun mark => (_, mark)) same, tail⟩

private theorem completed_prefix_full (entry : Tuple m.Val args) (locals : Locals m.Val past)
    (mark : Marking m whole) {output : Tuple m.Val outs}
    (done : finished m whole entry (full locals) mark = some output) :
    ∃ result, finished m front entry (full locals) (cut.observe m mark) = some result := by
  induction cut with
  | stop wires _ => exact ⟨_, read_full wires entry locals⟩
  | bind _ _ _ ih =>
    cases phase : mark.1 with
    | pending | waiting => simp [finished, phase] at done
    | done value =>
      obtain ⟨result, prefixDone⟩ := ih (locals.snoc value) mark.2
        (by simpa only [finished, phase, full_snoc] using done)
      exact ⟨result, by simpa only [Cut.observe, finished, phase, full_snoc] using prefixDone⟩

theorem completed_prefix
    {front : Term Op args [] frontSigs bank} {whole : Term Op args [] wholeSigs outs}
    {tail : Term Op args (extend [] frontSigs) tailSigs outs} (cut : Cut front whole tail)
    (m : Model.{u, v, w} Op) (entry : Tuple m.Val args) (mark : Marking m whole)
    {output : Tuple m.Val outs} (done : finished m whole entry PUnit.unit mark = some output) :
    ∃ result, finished m front entry PUnit.unit (cut.observe m mark) = some result :=
  completed_prefix_full cut m entry PUnit.unit mark done

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Proofs

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Proofs

open RVSDG.Petri (Tokens)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

theorem finished_no_step (m : Model.{u, v, w} Op) (term : Term Op args past sigs outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past) {before after : Marking m term}
    {output : Tuple m.Val outs} (done : finished m term entry tokens before = some output)
    (step : Fire m term entry tokens before after) : False := by
  induction step with
  | primitive | enter | advance | commit | restart =>
    cases done
  | @later _ _ _ _ _ _ _ _ _ _ vertex _ _ firing ih =>
    cases vertex with
    | pending | waiting => cases done
    | done value => exact ih done

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Proofs
