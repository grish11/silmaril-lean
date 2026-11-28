module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs

/-! Enumerate candidate firings with certificates in the original relation. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay

open RVSDG.Petri (Tokens Vertex)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}

/-- Every candidate carries the original hierarchical firing that produces it. -/
def successors (m : Model.{u, v, w} Op) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → (entry : Tuple m.Val args) → (tokens : Tokens m.Val past) →
    (before : Marking m term) → List {after : Marking m term // Fire m term entry tokens before after}
  | _, _, _, _, .ret _, _, _, _ => []
  | _, _, _, _, .bind node children rest, entry, tokens, before => by
    obtain ⟨vertex, tail⟩ := before
    let later : List {after : Marking m (.bind node children rest) //
        Fire m (.bind node children rest) entry tokens (vertex, tail) after} :=
      (successors m rest entry (tokens.snoc vertex.outputs) tail).map
        (fun move => ⟨(vertex, move.val), Fire.later move.property⟩)
    cases vertex with
    | pending =>
      exact match read : RVSDG.Petri.read node.inputs entry tokens with
      | none => later
      | some input =>
        let simple := match ran : primitive m node.kind input with
          | none => []
          | some output => [⟨(.done output, tail), Fire.primitive read ran⟩]
        let enter := match chosen : activate m node.kind input with
          | none => []
          | some (arm, bank) =>
            [⟨(.waiting arm (bank, pending m (children arm)), tail), Fire.enter read chosen⟩]
        simple ++ enter ++ later
    | waiting arm active =>
      obtain ⟨bank, child⟩ := active
      let Candidate := {after : Marking m (.bind node children rest) //
        Fire m (.bind node children rest) entry tokens (.waiting arm (bank, child), tail) after}
      let advance : List Candidate := (successors m (children arm) bank PUnit.unit child).map
        (fun move => ⟨(.waiting arm (bank, move.val), tail), Fire.advance move.property⟩)
      let consume : List Candidate := match done : finished m (children arm) bank PUnit.unit child with
        | none => []
        | some packet =>
          match exit : route m node.kind arm packet with
          | .inl output => [⟨(.done output, tail), Fire.commit done exit⟩]
          | .inr feedback =>
            match restart : activate m node.kind feedback with
            | none => []
            | some (j, next) =>
              if same : j = arm then by
                subst j
                exact [⟨(.waiting arm (next, pending m (children arm)), tail), Fire.restart done exit restart⟩]
              else []
      exact advance ++ consume ++ later
    | done _ => exact later

def tupleDecEq {Ty : Type u} {F : Ty → Type w}
    (colourEq : (ty : Ty) → DecidableEq (F ty)) : (ports : Ports Ty) → DecidableEq (Tuple F ports)
  | [], .nil, .nil => isTrue rfl
  | t :: ports, .cons a as, .cons b bs =>
    match colourEq t a b, tupleDecEq colourEq ports as bs with
    | isTrue head, isTrue tail => isTrue (by cases head; cases tail; rfl)
    | isFalse unequal, _ => isFalse (fun eq => by cases eq; exact unequal rfl)
    | _, isFalse unequal => isFalse (fun eq => by cases eq; exact unequal rfl)

def vertexDecEq {Output : Type u} {arity : Nat} {Child : Fin arity → Type w}
    (outputEq : DecidableEq Output) (childEq : (i : Fin arity) → DecidableEq (Child i)) :
    DecidableEq (Vertex Output Child) := fun a b => by
  cases a with
  | pending => cases b <;> first | exact isTrue rfl | exact isFalse (fun h => by cases h)
  | done x =>
    cases b with
    | pending | waiting => exact isFalse (fun h => by cases h)
    | done y =>
      exact decidable_of_iff (x = y) ⟨congrArg Vertex.done, fun eq => by cases eq; rfl⟩
  | waiting i x =>
    cases b with
    | pending | done => exact isFalse (fun h => by cases h)
    | waiting j y =>
      by_cases same : i = j
      · subst j
        letI := childEq i
        exact decidable_of_iff (x = y) ⟨congrArg (Vertex.waiting i), fun eq => by cases eq; rfl⟩
      · exact isFalse (fun eq => by cases eq; exact same rfl)

def markingDecEq (m : Model.{u, v, w} Op) (colourEq : (t : PortType V S) → DecidableEq (m.Val t)) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    (term : Term Op args past sigs outs) → DecidableEq (Marking m term)
  | _, _, _, _, .ret _ => inferInstanceAs (DecidableEq PUnit)
  | _, _, _, _, .bind (head := head) node children rest => by
    letI : DecidableEq (Tuple m.Val node.kind.entry) := tupleDecEq colourEq _
    letI : DecidableEq (Marking m rest) := markingDecEq m colourEq rest
    letI : DecidableEq (Vertex (Tuple m.Val head)
        (fun i => Tuple m.Val node.kind.entry × Marking m (children i))) :=
      vertexDecEq (tupleDecEq colourEq head) fun i => by
        letI : DecidableEq (Marking m (children i)) := markingDecEq m colourEq (children i)
        infer_instance
    exact inferInstanceAs (DecidableEq (_ × Marking m rest))

/-- Check the exact supplied successor marking against certified candidates. -/
def checkFire (m : Model.{u, v, w} Op) (colourEq : (t : PortType V S) → DecidableEq (m.Val t))
    {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
    (term : Term Op args past sigs outs) (entry : Tuple m.Val args) (tokens : Tokens m.Val past)
    (before after : Marking m term) : Option (PLift (Fire m term entry tokens before after)) :=
  letI := markingDecEq m colourEq term
  (successors m term entry tokens before).findSome? fun move =>
    if same : move.val = after then some ⟨same ▸ move.property⟩ else none

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay
