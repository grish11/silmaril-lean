module

public import Silmaril.SSA.RVSDG.Petri.Defs
public import Silmaril.SSA.RVSDG.Thms
import Silmaril.Proofs.SSA.RVSDG.Petri.Colours

public section

namespace Silmaril.SSA.RVSDG.Petri.Proofs

universe u v w

open Relation (ReflTransGen)

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args ins outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

private theorem eval_primitive (m : Model.{u, v, w} Op) (shape : Shape Op ins outs)
    (runChild : Fin shape.regionCount → Tuple m.Val shape.entry → Tuple m.Val shape.exit)
    (input : Tuple m.Val ins) {output : Tuple m.Val outs}
    (h : primitive m shape input = some output) : shape.eval m runChild input = output := by
  cases shape with
  | simple opcode => exact Option.some.inj h
  | gamma extra => cases h

private theorem eval_selected (m : Model.{u, v, w} Op) (shape : Shape Op ins outs)
    (runChild : Fin shape.regionCount → Tuple m.Val shape.entry → Tuple m.Val shape.exit)
    (input : Tuple m.Val ins) {arm : Fin shape.regionCount} {received : Tuple m.Val shape.entry}
    (h : select m shape input = some (arm, received)) :
    shape.eval m runChild input = publish m shape arm (runChild arm received) := by
  cases shape with
  | simple opcode => exact arm.elim0
  | gamma extra =>
    cases input with
    | cons choice entry =>
      have equal := Option.some.inj h
      cases equal
      rfl

/-- Complete the unmarked part in number order, using already published colours and
the live child's saved entry tuple. This is only a proof interpretation of a marking. -/
private def residual (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → Tuple m.Val args → Locals m.Val past →
    Marking m term → Tuple m.Val outs
  | _, _, _, _, .ret results, entry, locals, _ => results.read entry locals
  | _, _, _, _, .bind node children rest, entry, locals, marking =>
    let upstream := match marking.1 with
      | .pending => node.shape.eval m
          (fun j input => (children j).eval m (past := []) input PUnit.unit)
          (node.inputs.read entry locals)
      | .waiting arm (input, child) =>
          publish m node.shape arm (residual m (past := []) (children arm) input PUnit.unit child)
      | .done output => output
    residual m rest entry (locals.snoc upstream) marking.2

private theorem residual_pending (m : Model.{u, v, w} Op) (term : Term Op args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    residual m term entry locals (pending m term) = term.eval m entry locals := by
  induction term with
  | ret => rfl
  | bind node children rest _ ih => exact ih entry _

private theorem finished_residual (m : Model.{u, v, w} Op) (term : Term Op args past sigs outs)
    (entry : Tuple m.Val args) {tokens : Tokens m.Val past} {locals : Locals m.Val past}
    (agrees : Agrees tokens locals) {marking : Marking m term} {output : Tuple m.Val outs}
    (h : finished m term entry tokens marking = some output) :
    residual m term entry locals marking = output := by
  induction term with
  | ret results => exact read_sound results entry agrees h
  | bind node children rest _ ih =>
    obtain ⟨vertex, tail⟩ := marking
    cases vertex with
    | pending | waiting => cases h
    | done values =>
      exact ih entry (agrees_snoc agrees (fun _ p _ => agrees_present values p)) h

private theorem residual_step (m : Model.{u, v, w} Op) {term : Term Op args past sigs outs}
    {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {locals : Locals m.Val past}
    {before after : Marking m term} (step : Fire m term entry tokens before after)
    (agrees : Agrees tokens locals) :
    residual m term entry locals before = residual m term entry locals after := by
  induction step with
  | @primitive args head outs past sigs node children rest entry tokens tail input output ready fired =>
    have inputs := read_sound node.inputs entry agrees ready
    simp only [residual, inputs, eval_primitive m node.shape _ input fired]
  | @enter args head outs past sigs node children rest entry tokens tail input arm received ready guard =>
    have inputs := read_sound node.inputs entry agrees ready
    simp only [residual, inputs, eval_selected m node.shape _ input guard]
    rw [residual_pending m (past := []) (children arm) received PUnit.unit]
  | advance step ih =>
    simp only [residual, ih (locals := PUnit.unit) (by trivial : Agrees (past := []) (F := m.Val) PUnit.unit PUnit.unit)]
  | commit ready =>
    simp only [residual, finished_residual m _ _ (by trivial : Agrees (past := []) (F := m.Val) PUnit.unit PUnit.unit) ready]
  | later step ih =>
    rename_i node children rest entry tokens vertex before after
    cases vertex with
    | pending =>
      apply ih
      exact agrees_snoc agrees (fun _ p _ hx => by cases (get_absent p).symm.trans hx)
    | waiting arm child =>
      obtain ⟨input, marking⟩ := child
      apply ih
      exact agrees_snoc agrees (fun _ p _ hx => by cases (get_absent p).symm.trans hx)
    | done output =>
      exact ih (agrees_snoc agrees (fun _ p _ => agrees_present output p))

theorem fire_unfinished (m : Model.{u, v, w} Op) {term : Term Op args past sigs outs}
    {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {before after : Marking m term}
    (step : Fire m term entry tokens before after) :
    finished m term entry tokens before = none := by
  induction step with
  | primitive | enter | advance | commit => rfl
  | @later _ _ _ _ _ _ _ _ _ _ vertex _ _ _ ih =>
    cases vertex with
    | pending | waiting => rfl
    | done => exact ih

private theorem residual_reach (m : Model.{u, v, w} Op) {term : Term Op args past sigs outs}
    {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {locals : Locals m.Val past}
    (agrees : Agrees tokens locals) {before after : Marking m term}
    (steps : ReflTransGen (Fire m term entry tokens) before after) :
    residual m term entry locals before = residual m term entry locals after := by
  induction steps with
  | refl => rfl
  | tail _ step ih => exact ih.trans (residual_step m step agrees)

theorem sound (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) {output : Tuple m.Val outs} (completes : Finishes m graph input output) :
    graph.run m input = output := by
  obtain ⟨marking, steps, finished⟩ := completes
  have agrees : Agrees (past := []) (F := m.Val) PUnit.unit PUnit.unit := trivial
  rw [← Graph.run_toTerm]
  exact (residual_pending m graph.toTerm input PUnit.unit).symm.trans
    ((residual_reach m agrees steps).trans (finished_residual m graph.toTerm input agrees finished))

private theorem vertex_enabled (m : Model.{u, v, w} Op) (shape : Shape Op ins outs)
    (input : Tuple m.Val ins) :
    (∃ output, primitive m shape input = some output) ∨
      ∃ arm received, select m shape input = some (arm, received) := by
  cases shape with
  | simple op => exact .inl ⟨m.run op input, rfl⟩
  | gamma extra => cases input with | cons choice entry => exact .inr ⟨choice.down, entry, rfl⟩

private theorem complete_from (m : Model.{u, v, w} Op) (term : Term Op args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    ∃ marking, ReflTransGen (Fire m term entry (full locals)) (pending m term) marking ∧
      finished m term entry (full locals) marking = some (term.eval m entry locals) := by
  induction term with
  | ret results => exact ⟨PUnit.unit, .refl, read_full results entry locals⟩
  | @bind args head outs past sigs node children rest ihChild ihRest =>
    let input := node.inputs.read entry locals
    let runChild := fun j received => (children j).eval m (past := []) received PUnit.unit
    let output := node.shape.eval m runChild input
    let fire := Fire m (Term.bind node children rest) entry (full locals)
    have ready : read node.inputs entry (full locals) = some input := read_full node.inputs entry locals
    have headSteps : ReflTransGen fire (.pending, pending m rest) (.done output, pending m rest) := by
      rcases vertex_enabled m node.shape input with ⟨value, fired⟩ | ⟨arm, received, guard⟩
      · rw [show output = value from eval_primitive m node.shape runChild input fired]
        exact .single (.primitive ready fired)
      · obtain ⟨child, childSteps, childResult⟩ := ihChild arm received PUnit.unit
        let waiting (mark : Marking m (children arm)) : Marking m (.bind node children rest) :=
          (.waiting arm (received, mark), pending m rest)
        have advances : ReflTransGen fire (waiting (pending m (children arm))) (waiting child) :=
          childSteps.lift (p := fire) waiting (fun _ _ step => Fire.advance step)
        rw [show output = publish m node.shape arm (runChild arm received)
          from eval_selected m node.shape runChild input guard]
        exact (advances.head (.enter ready guard)).tail (.commit childResult)
    obtain ⟨tail, tailSteps, tailResult⟩ := ihRest entry (locals.snoc output)
    let done (mark : Marking m rest) : Marking m (.bind node children rest) := (.done output, mark)
    have restSteps : ReflTransGen fire (done (pending m rest)) (done tail) :=
      tailSteps.lift (p := fire) done (fun before after step => by
        change fire (done before) (done after)
        apply Fire.later
        simpa only [Vertex.outputs, ← full_snoc] using step)
    refine ⟨(.done output, tail), headSteps.trans restSteps, ?_⟩
    simpa only [finished, Term.eval, ← full_snoc] using tailResult

theorem complete (m : Model.{u, v, w} Op) (graph : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) : Finishes m graph input (graph.run m input) := by
  rw [← Graph.run_toTerm]
  exact complete_from m graph.toTerm input PUnit.unit

end Silmaril.SSA.RVSDG.Petri.Proofs
