module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.Proofs.SSA.RVSDG.Petri.Colours

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Proofs

universe u v w

open Relation (ReflTransGen)
open RVSDG.Petri (Tokens Vertex read)
open RVSDG.Petri.Proofs (full full_snoc read_full)

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args head outs carried : Ports (PortType V S)}
variable {past sigs : List (Ports (PortType V S))}

private abbrev ChildrenComplete (m : Model.{u, v, w} Op) (node : Node Op args past head)
    (children : Children (Term Op) node) :=
  ∀ (arm : Fin node.kind.arity) (input : Tuple m.Val node.kind.entry) (output : Tuple m.Val node.kind.exit),
    (children arm).Returns m input output →
      ∃ mark, ReflTransGen (Fire m (past := []) (children arm) input PUnit.unit)
        (pending m (children arm)) mark ∧
        finished m (past := []) (children arm) input PUnit.unit mark = some output

private theorem lift_child (m : Model.{u, v, w} Op) {node : Node Op args past head}
    {children : Children (Term Op) node} {rest : Term Op args (past ++ [head]) sigs outs}
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (tail : Marking m rest)
    (arm : Fin node.kind.arity) (input : Tuple m.Val node.kind.entry) (mark : Marking m (children arm))
    (steps : ReflTransGen (Fire m (past := []) (children arm) input PUnit.unit) (pending m (children arm)) mark) :
    ReflTransGen (Fire m (.bind node children rest) entry tokens)
      (.waiting arm (input, pending m (children arm)), tail) (.waiting arm (input, mark), tail) :=
  steps.lift (p := Fire m (.bind node children rest) entry tokens)
    (fun mark => (.waiting arm (input, mark), tail)) (fun _ _ step => Fire.advance step)

private theorem loop_steps (m : Model.{u, v, w} Op) (wires : Wires args past carried)
    (bodySigs : Fin 1 → List (Ports (PortType V S)))
    (children : (i : Fin 1) → Term Op carried [] (bodySigs i) (Theta.BodyResults carried))
    (rest : Term Op args (past ++ [carried]) sigs outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    (childComplete : ChildrenComplete m (⟨carried, .theta carried, wires, bodySigs⟩ : Node Op args past carried)
      children)
    (input output : Tuple m.Val carried)
    (execution : Theta.Iterate
      (fun i again o => (children 0).Returns m i (Theta.bodyResult m again o)) input output) :
    let node : Node Op args past carried := ⟨carried, .theta carried, wires, bodySigs⟩
    ReflTransGen (Fire m (.bind node children rest) entry tokens)
      (.waiting (0 : Fin 1) (input, pending m (children 0)), pending m rest)
      (.done output, pending m rest) := by
  let node : Node Op args past carried := ⟨carried, .theta carried, wires, bodySigs⟩
  induction execution with
  | @stop start finish ran =>
    obtain ⟨mark, steps, done⟩ := childComplete (0 : Fin 1) start (Theta.bodyResult m false finish) ran
    exact (lift_child m (node := node) (children := children) (rest := rest) entry tokens (pending m rest) (0 : Fin 1) start mark steps).tail (.commit done rfl)
  | @again start next finish ran more ih =>
    obtain ⟨mark, steps, done⟩ := childComplete (0 : Fin 1) start (Theta.bodyResult m true next) ran
    exact ((lift_child m (node := node) (children := children) (rest := rest) entry tokens (pending m rest) (0 : Fin 1) start mark steps).tail
      (.restart done rfl rfl)).trans ih

private theorem head_steps (m : Model.{u, v, w} Op) (node : Node Op args past head)
    (children : Children (Term Op) node) (rest : Term Op args (past ++ [head]) sigs outs)
    (entry : Tuple m.Val args) (tokens : Tokens m.Val past) (childComplete : ChildrenComplete m node children)
    (input : Tuple m.Val node.ins) (output : Tuple m.Val head)
    (ready : read node.inputs entry tokens = some input)
    (execution : node.kind.Exec m (fun i x y => (children i).Returns m x y) input output) :
    ReflTransGen (Fire m (.bind node children rest) entry tokens)
      (.pending, pending m rest) (.done output, pending m rest) := by
  obtain ⟨ins, kind, wires, bodySigs⟩ := node
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode =>
      exact .single (.primitive ready (congrArg some execution))
    | gamma extra =>
      cases input with
      | cons tag received =>
        let node : Node Op args past head := ⟨_, .base (.gamma extra), wires, bodySigs⟩
        obtain ⟨mark, steps, done⟩ := childComplete tag.down received output execution
        exact ((lift_child m (node := node) (children := children) (rest := rest) entry tokens (pending m rest) tag.down received mark steps).head
          (.enter ready rfl)).tail (.commit done rfl)
  | theta =>
    exact (loop_steps m wires bodySigs children rest entry tokens childComplete input output execution).head
      (.enter ready rfl)

private theorem complete_term (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs)
    (execution : t.Exec m entry locals output) :
    ∃ mark, ReflTransGen (Fire m t entry (full locals)) (pending m t) mark ∧
      finished m t entry (full locals) mark = some output := by
  induction t with
  | ret wires =>
    exact ⟨PUnit.unit, .refl, (read_full wires entry locals).trans (congrArg some execution)⟩
  | @bind args head outs past sigs node children rest childIH restIH =>
    obtain ⟨value, first, remaining⟩ := execution
    have completeChild : ChildrenComplete m node children :=
      fun arm i o run => childIH arm i PUnit.unit o run
    have headRun := head_steps m node children rest entry (full locals) completeChild
      (node.inputs.read entry locals) value (read_full node.inputs entry locals) first
    obtain ⟨tail, steps, finishedTail⟩ := restIH entry (locals.snoc value) output remaining
    let completeHead (mark : Marking m rest) : Marking m (.bind node children rest) := (.done value, mark)
    have tailRun : ReflTransGen (Fire m (.bind node children rest) entry (full locals))
        (completeHead (pending m rest)) (completeHead tail) :=
      steps.lift (p := Fire m (.bind node children rest) entry (full locals)) completeHead
        (fun before after step => by
          change Fire m (.bind node children rest) entry (full locals) (completeHead before) (completeHead after)
          apply Fire.later
          simpa only [Vertex.outputs, ← full_snoc] using step)
    refine ⟨completeHead tail, headRun.trans tailRun, ?_⟩
    simpa only [completeHead, finished, ← full_snoc] using finishedTail

theorem complete (m : Model.{u, v, w} Op) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs)
    (execution : g.toTerm.Returns m input output) : Finishes m g input output :=
  complete_term m g.toTerm input PUnit.unit output execution

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Proofs
