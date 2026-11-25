module

public import Silmaril.SSA.RVSDG.NestedTheta.Defs

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args head outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

private theorem region_congr (nodes nodes' : Nodes Op args past sigs)
    (children : (i : Fin sigs.length) → Children (Graph Op) (nodes i))
    (children' : (i : Fin sigs.length) → Children (Graph Op) (nodes' i))
    (results : Wires args (extend past sigs) outs)
    (h : ∀ i, (⟨nodes i, children i⟩ : Σ n, Children (Graph Op) n) = ⟨nodes' i, children' i⟩) :
    Graph.region nodes children results = Graph.region nodes' children' results :=
  congrArg (fun table => Graph.region (fun i => (table i).1) (fun i => (table i).2) results)
    (funext h)

private theorem prepend_split (nodes : Nodes Op args past (head :: sigs))
    (children : (i : Fin (head :: sigs).length) → Children (Graph Op) (nodes i))
    (results : Wires args (extend past (head :: sigs)) outs) :
    (Graph.region (fun i : Fin sigs.length => nodes i.succ) (fun i => children i.succ) results).prepend
        (nodes 0) (children 0) = Graph.region nodes children results := by
  unfold Graph.prepend
  apply region_congr
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · rfl

private theorem toTerm_prepend (node : Node Op args past head) (children : Children (Graph Op) node)
    (rest : Graph Op args (past ++ [head]) sigs outs) :
    (rest.prepend node children).toTerm =
      .bind node (fun j => (children j).toTerm) rest.toTerm := by
  cases rest
  rfl

theorem toTerm_toGraph (term : Term Op args past sigs outs) : term.toGraph.toTerm = term := by
  induction term with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    rw [Term.toGraph, toTerm_prepend, ihRest]
    exact congrArg (fun arms => Term.bind node arms rest) (funext ihChildren)

private theorem toGraph_fromTable (past sigs : List (Ports (PortType V S)))
    (nodes : Nodes Op args past sigs) (children : (i : Fin sigs.length) → Children (Term Op) (nodes i))
    (results : Wires args (extend past sigs) outs) :
    (Term.fromTable past sigs nodes children results).toGraph =
      .region nodes (fun i j => (children i j).toGraph) results := by
  induction sigs generalizing past with
  | nil =>
    simp only [Term.fromTable, Term.toGraph]
    apply region_congr
    exact fun i => i.elim0
  | cons head tail ih =>
    simp only [Term.fromTable, Term.toGraph]
    refine (congrArg (Graph.prepend (nodes 0) (fun j => (children 0 j).toGraph))
      (ih (past ++ [head]) (fun i => nodes i.succ) (fun i => children i.succ) results)).trans ?_
    exact prepend_split nodes (fun i j => (children i j).toGraph) results

theorem toGraph_toTerm (graph : Graph Op args past sigs outs) : graph.toTerm.toGraph = graph := by
  induction graph with
  | region nodes children results ih =>
    rw [Graph.toTerm, toGraph_fromTable]
    exact congrArg (fun arms => Graph.region nodes arms results) (funext fun i => funext (ih i))

private theorem eval_fromTable (m : Model.{u, v, w} Op) (fuel : Nat) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (locals : Locals m.Val past)
    (nodes : Nodes Op args past sigs) (children : (i : Fin sigs.length) → Children (Term Op) (nodes i))
    (results : Wires args (extend past sigs) outs) :
    (Term.fromTable past sigs nodes children results).eval m fuel entry locals =
      evalTable m fuel entry past sigs locals nodes
        (fun i j input => (children i j).eval m fuel (past := []) input PUnit.unit) results := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    simp only [Term.fromTable, Term.eval, evalTable]
    congr 1
    funext result
    apply ih

theorem eval_toTerm (graph : Graph Op args past sigs outs) (m : Model.{u, v, w} Op) (fuel : Nat)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    graph.toTerm.eval m fuel entry locals = graph.eval m fuel entry locals := by
  induction graph with
  | region nodes children results ih =>
    rw [Graph.toTerm, eval_fromTable, Graph.eval]
    congr 1
    exact funext fun i => funext fun j => funext fun input => ih i j input PUnit.unit

end Silmaril.SSA.RVSDG.NestedTheta.Proofs
