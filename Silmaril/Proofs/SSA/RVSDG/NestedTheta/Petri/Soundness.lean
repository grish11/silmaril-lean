module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.Proofs.SSA.RVSDG.Petri.Colours
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Completeness

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Proofs

universe u v w

open Relation (ReflTransGen)
open RVSDG.Petri (Tokens Vertex)
open RVSDG.Petri.Proofs (Agrees agrees_snoc agrees_present get_absent read_sound full full_snoc read_full)

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args ins outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

private abbrev ChildExec (m : Model.{u, v, w} Op) (kind : Kind Op ins outs) :=
  Fin kind.arity → Tuple m.Val kind.entry → Tuple m.Val kind.exit → Prop

private def afterBody (m : Model.{u, v, w} Op) (kind : Kind Op ins outs) (fresh : ChildExec m kind) :
    Sum (Tuple m.Val outs) (Tuple m.Val ins) → Tuple m.Val outs → Prop
  | .inl completed, result => completed = result
  | .inr next, result => kind.Exec m fresh next result

private def waiting (m : Model.{u, v, w} Op) (kind : Kind Op ins outs) (fresh : ChildExec m kind)
    (arm : Fin kind.arity) (live : Tuple m.Val kind.exit → Prop) (output : Tuple m.Val outs) : Prop :=
  ∃ returned, live returned ∧ afterBody m kind fresh (route m kind arm returned) output

private theorem tag_decode (m : Model.{u, v, w} Op) {carried : Ports (PortType V S)}
    (tag : ULift.{w} (Fin 2)) (next : Tuple m.Val carried) :
    (Tuple.cons tag next : Tuple m.Val (Theta.BodyResults carried)) =
      Theta.bodyResult m (tag.down.val == 1) next := by
  obtain ⟨tag⟩ := tag
  exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)) tag

private theorem waiting_initial (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    (fresh : ChildExec m kind) (input : Tuple m.Val ins) (arm : Fin kind.arity)
    (received : Tuple m.Val kind.entry) (output : Tuple m.Val outs)
    (guard : activate m kind input = some (arm, received)) :
    waiting m kind fresh arm (fresh arm received) output ↔ kind.Exec m fresh input output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode => exact arm.elim0
    | gamma extra =>
      cases input with
      | cons tag entry =>
        have selected := Option.some.inj guard
        cases selected
        constructor
        · rintro ⟨value, live, eq⟩
          exact (show value = output from eq) ▸ live
        · intro h
          exact ⟨output, h, rfl⟩
  | theta =>
    have selected := Option.some.inj guard
    cases selected
    constructor
    · rintro ⟨returned, live, after⟩
      cases returned with
      | cons tag next =>
        rw [tag_decode m tag next] at live
        change afterBody m (.theta _) fresh
          (if tag.down.val == 1 then .inr next else .inl next) output at after
        cases test : tag.down.val == 1 with
        | false =>
          simp [test, afterBody] at after
          rw [test] at live
          exact after ▸ Theta.Iterate.stop live
        | true =>
          simp [test, afterBody] at after
          rw [test] at live
          exact Theta.Iterate.again live after
    · intro execution
      cases execution with
      | stop finished => exact ⟨Theta.bodyResult m false _, finished, rfl⟩
      | again step more => exact ⟨Theta.bodyResult m true _, step, more⟩

private theorem waiting_completed (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    (fresh : ChildExec m kind) (arm : Fin kind.arity) (live : Tuple m.Val kind.exit → Prop)
    (returned : Tuple m.Val kind.exit) (output : Tuple m.Val outs)
    (exactReturn : ∀ result, live result ↔ returned = result) :
    waiting m kind fresh arm live output ↔ afterBody m kind fresh (route m kind arm returned) output := by
  constructor
  · rintro ⟨result, run, thenRun⟩
    have same := (exactReturn result).1 run
    subst result
    exact thenRun
  · intro after
    exact ⟨returned, (exactReturn returned).2 rfl, after⟩

private theorem primitive_exact (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    (fresh : ChildExec m kind) (input : Tuple m.Val ins) {value : Tuple m.Val outs}
    (ran : primitive m kind input = some value) (output : Tuple m.Val outs) :
    kind.Exec m fresh input output ↔ value = output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode =>
      have result := Option.some.inj ran
      change m.run opcode input = output ↔ value = output
      rw [result]
    | gamma extra => cases ran
  | theta => cases ran

/-- A partial marking's possible result is a relational interpretation of
the work that remains. It need not admit a result. -/
private def residual (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → Tuple m.Val args → Locals m.Val past →
    Marking m term → Tuple m.Val outs → Prop
  | _, _, _, _, .ret wires, entry, locals, _, output => wires.read entry locals = output
  | _, _, _, _, .bind node children rest, entry, locals, marks, output =>
    let fresh := fun i x y => (children i).Exec m (past := []) x PUnit.unit y
    let head : Tuple m.Val _ → Prop := match marks.1 with
      | .pending => node.kind.Exec m fresh (node.inputs.read entry locals)
      | .done value => (value = ·)
      | .waiting arm (input, child) =>
        waiting m node.kind fresh arm (residual m (past := []) (children arm) input PUnit.unit child)
    ∃ value, head value ∧ residual m rest entry (locals.snoc value) marks.2 output

private theorem residual_pending (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs) :
    residual m t entry locals (pending m t) output ↔ t.Exec m entry locals output := by
  induction t with
  | ret => rfl
  | bind node children rest _ ih =>
    simp only [residual, pending, Term.Exec]
    exact exists_congr fun value => and_congr Iff.rfl (ih entry (locals.snoc value) output)

private theorem finished_residual (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs)
    (entry : Tuple m.Val args) {tokens : Tokens m.Val past} {locals : Locals m.Val past}
    (agrees : Agrees tokens locals) {marking : Marking m t} {returned : Tuple m.Val outs}
    (h : finished m t entry tokens marking = some returned) (output : Tuple m.Val outs) :
    residual m t entry locals marking output ↔ returned = output := by
  induction t with
  | ret wires =>
    change wires.read entry locals = output ↔ returned = output
    rw [read_sound wires entry agrees h]
  | bind node children rest _ ih =>
    obtain ⟨vertex, tail⟩ := marking
    cases vertex with
    | pending | waiting => cases h
    | done value =>
      have tailResult := ih entry
        (agrees_snoc agrees (fun _ p _ => agrees_present value p)) h output
      constructor
      · rintro ⟨found, equal, possible⟩
        subst found
        exact tailResult.1 possible
      · intro equal
        exact ⟨value, rfl, tailResult.2 equal⟩

private theorem residual_step (m : Model.{u, v, w} Op) {t : Term Op args past sigs outs}
    {entry : Tuple m.Val args} {tokens : Tokens m.Val past} {locals : Locals m.Val past}
    {before after : Marking m t} (step : Fire m t entry tokens before after)
    (agrees : Agrees tokens locals) (output : Tuple m.Val outs) :
    residual m t entry locals before output ↔ residual m t entry locals after output := by
  induction step with
  | @primitive args head outs past sigs node children rest entry tokens tail input value ready ran =>
    simp only [residual, read_sound node.inputs entry agrees ready]
    exact exists_congr fun observed => and_congr (primitive_exact m node.kind _ input ran observed) Iff.rfl
  | @enter args head outs past sigs node children rest entry tokens tail input arm received ready guard =>
    simp only [residual, read_sound node.inputs entry agrees ready]
    have starts : residual m (past := []) (children arm) received PUnit.unit
        (pending m (children arm)) =
        (fun y => (children arm).Exec m (past := []) received PUnit.unit y) :=
      funext fun y => propext (residual_pending m (children arm) received PUnit.unit y)
    rw [starts]
    exact exists_congr fun observed =>
      and_congr (waiting_initial m node.kind _ input arm received observed guard).symm Iff.rfl
  | advance step ih =>
    have runs := funext fun y => propext (ih (locals := PUnit.unit)
      (by trivial : Agrees (past := []) (F := m.Val) PUnit.unit PUnit.unit) y)
    simp only [residual, runs]
  | @commit args head outs past sigs node children rest entry tokens tail arm received child returned value ready decide =>
    simp only [residual]
    apply exists_congr
    intro observed
    refine and_congr ?_ Iff.rfl
    have live := finished_residual m (children arm) received
      (by trivial : Agrees (past := []) (F := m.Val) PUnit.unit PUnit.unit) ready
    exact (waiting_completed m node.kind _ arm _ returned observed live).trans
      (by rw [decide]; rfl)
  | @restart args head outs past sigs node children rest entry tokens tail arm received next child returned
      feedback ready decide entered =>
    simp only [residual]
    apply exists_congr
    intro observed
    refine and_congr ?_ Iff.rfl
    have live := finished_residual m (children arm) received
      (by trivial : Agrees (past := []) (F := m.Val) PUnit.unit PUnit.unit) ready
    have starts : residual m (past := []) (children arm) next PUnit.unit
        (pending m (children arm)) =
        (fun y => (children arm).Exec m (past := []) next PUnit.unit y) :=
      funext fun y => propext (residual_pending m (children arm) next PUnit.unit y)
    rw [starts]
    refine (waiting_completed m node.kind _ arm _ returned observed live).trans ?_
    rw [decide]
    exact (waiting_initial m node.kind _ feedback arm next observed entered).symm
  | @later args head outs past sigs node children rest entry tokens vertex before after step ih =>
    cases vertex <;> simp only [residual]
    all_goals
      apply exists_congr
      intro value
      apply and_congr_right
      intro head
      apply ih
    case pending | waiting => exact agrees_snoc agrees (fun _ p _ h => by cases (get_absent p).symm.trans h)
    case done published =>
      change published = value at head
      subst value
      exact agrees_snoc agrees (fun _ p _ => agrees_present published p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complete_residual (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (mark : Marking m t) (output : Tuple m.Val outs)
    (run : residual m t entry locals mark output) :
    ∃ final, ReflTransGen (Fire m t entry (full locals)) mark final ∧
      finished m t entry (full locals) final = some output := by
  induction t with
  | ret wires =>
    exact ⟨mark, .refl, (read_full wires entry locals).trans (congrArg some run)⟩
  | @bind args head outs past sigs node children rest childIH restIH =>
    obtain ⟨vertex, tail⟩ := mark
    rw [residual] at run
    obtain ⟨value, headRun, tailRun⟩ := run
    have completeChild : ChildrenComplete m node children :=
      fun arm i o h => childIH arm i PUnit.unit (pending m (children arm)) o
        ((residual_pending m (children arm) i PUnit.unit o).2 h)
    have headSteps : ReflTransGen (Fire m (.bind node children rest) entry (full locals))
        (vertex, tail) (.done value, tail) := by
      cases vertex with
      | pending =>
        exact head_steps m node children rest entry (full locals) tail completeChild
          (node.inputs.read entry locals) value (read_full node.inputs entry locals) headRun
      | done published =>
        change published = value at headRun
        subst published
        exact .refl
      | waiting arm active =>
        obtain ⟨received, child⟩ := active
        obtain ⟨returned, childRun, after⟩ := headRun
        obtain ⟨final, steps, done⟩ := childIH arm received PUnit.unit child returned childRun
        have advance := steps.lift
          (p := Fire m (.bind node children rest) entry (full locals))
          (fun mark => (.waiting arm (received, mark), tail)) (fun _ _ step => Fire.advance step)
        cases routing : route m node.kind arm returned with
        | inl published =>
          rw [routing] at after
          change published = value at after
          subst published
          exact advance.tail (.commit done routing)
        | inr next =>
          obtain ⟨ins, kind, wires, bodySigs⟩ := node
          cases kind with
          | base shape => cases routing
          | theta =>
            have armZero : arm = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
            subst arm
            rw [routing] at after
            have reset := advance.tail (Fire.restart done routing rfl)
            -- Schedule the remaining iterations while leaving the enclosing tail as it was.
            exact reset.trans (loop_steps m wires bodySigs children rest entry (full locals)
              tail completeChild next value after)
    obtain ⟨final, steps, done⟩ := restIH entry (locals.snoc value) tail output tailRun
    have advance := steps.lift (p := Fire m (.bind node children rest) entry (full locals))
      (fun mark => (.done value, mark)) (fun _ _ step => by
        apply Fire.later
        simpa only [Vertex.outputs, ← full_snoc] using step)
    exact ⟨(.done value, final), headSteps.trans advance, by
      simpa only [finished, ← full_snoc] using done⟩

theorem complete_reached (m : Model.{u, v, w} Op) (t : Term Op args [] sigs outs)
    (entry : Tuple m.Val args) (output : Tuple m.Val outs) {mark : Marking m t}
    (steps : ReflTransGen (Fire m t entry PUnit.unit) (pending m t) mark)
    (run : t.Returns m entry output) :
    ∃ final, ReflTransGen (Fire m t entry PUnit.unit) mark final ∧
      finished m t entry PUnit.unit final = some output := by
  have agrees : Agrees (F := m.Val) (past := []) PUnit.unit PUnit.unit := trivial
  have remaining : residual m t entry PUnit.unit mark output := by
    induction steps with
    | refl => exact (residual_pending m t entry PUnit.unit output).2 run
    | tail _ step ih => exact (residual_step m step agrees output).1 ih
  exact complete_residual m t entry PUnit.unit mark output remaining

theorem sound (m : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) (h : Finishes m g input output) :
    g.toTerm.Returns m input output := by
  obtain ⟨mark, steps, done⟩ := h
  let empty : Locals m.Val [] := PUnit.unit
  have agrees : Agrees (F := m.Val) (past := []) PUnit.unit empty := trivial
  have remaining : residual m g.toTerm input empty (initial m g) output ↔
      residual m g.toTerm input empty mark output := by
    clear done
    induction steps with
    | refl => rfl
    | tail _ step ih => exact ih.trans (residual_step m step agrees output)
  exact (residual_pending m g.toTerm input empty output).1
    (remaining.2 ((finished_residual m g.toTerm input agrees done output).2 rfl))

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Proofs
