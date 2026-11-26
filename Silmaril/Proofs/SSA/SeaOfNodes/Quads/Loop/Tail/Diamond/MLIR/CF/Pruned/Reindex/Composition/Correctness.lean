module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Proofs

open RVSDG (Dialect PortType Port Tuple Wires)
open RVSDG.NestedTheta (Graph Term)

universe u v w

section Pull

variable {T : Type u} {F : T → Type w} {old mid new : List T}

theorem pull_trans (first : Permutation old mid) (second : Permutation mid new)
    (input : Tuple F new) :
    pull first (pull second input) = pull (first.trans second) input := by
  have ports :
      (fun {t} (port : Port old t) => (pull second input).get (first t port)) =
      (fun {t} (port : Port old t) => input.get (second t (first t port))) := by
    funext t port
    exact pull_get second input (first t port)
  exact congrArg (tabulate old) ports

end Pull

section Graph

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {old mid new outs : List (PortType V S)} {past sigs : List (List (PortType V S))}

theorem wires_refl (bundle : Wires old past outs) :
    wires (Permutation.refl old) bundle = bundle := by
  induction bundle with
  | nil => rfl
  | cons origin rest ih =>
    cases origin <;> exact congrArg (Tuple.cons _) ih

theorem wires_trans (first : Permutation old mid) (second : Permutation mid new)
    (bundle : Wires old past outs) :
    wires second (wires first bundle) = wires (first.trans second) bundle := by
  induction bundle with
  | nil => rfl
  | cons origin rest ih =>
    cases origin <;> exact congrArg (Tuple.cons _) ih

private theorem term_refl (body : Term Φ old past sigs outs) :
    term (Permutation.refl old) body = body := by
  induction body with
  | ret result =>
    simp only [term, wires_refl]
  | bind node children rest _ ih =>
    cases node with
    | mk ins kind inputs childSigs =>
      simp only [term, ih]
      exact congrArg (fun inputs => Term.bind ⟨ins, kind, inputs, childSigs⟩ children rest)
        (wires_refl inputs)

private theorem term_trans (first : Permutation old mid) (second : Permutation mid new)
    (body : Term Φ old past sigs outs) :
    term second (term first body) = term (first.trans second) body := by
  induction body with
  | ret result =>
    simp only [term, wires_trans]
  | bind node children rest _ ih =>
    simp only [term, ih]
    exact congrArg (fun inputs => Term.bind ⟨node.ins, node.kind, inputs, node.childSigs⟩ children
      (term (first.trans second) rest)) (wires_trans first second node.inputs)

theorem graph_refl (g : Graph Φ old past sigs outs) :
    graph (Permutation.refl old) g = g := by
  rw [graph, term_refl, Graph.toGraph_toTerm]

theorem graph_trans (first : Permutation old mid) (second : Permutation mid new)
    (g : Graph Φ old past sigs outs) :
    graph second (graph first g) = graph (first.trans second) g := by
  simp only [graph, Term.toTerm_toGraph, term_trans]

end Graph

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Proofs
