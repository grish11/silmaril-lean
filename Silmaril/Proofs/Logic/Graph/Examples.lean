module

public import Silmaril.Logic.Graph.Examples.Defs

@[expose] public section
namespace Silmaril.Logic.Graph.Examples.Proofs
open Silmaril.Semantics.Graph

theorem marker_loses_loop : markPresence withoutLoop = markPresence withLoop ∧ withoutLoop ≠ withLoop := by
  constructor
  · change (⟨_⟩ : RelGraph Unit) = ⟨_⟩
    congr 1
    funext a b
    apply propext
    have hab : a = b := by cases a; cases b; rfl
    simp [withoutLoop, withLoop, hab]
  · intro eq
    have impossible : False = True := congrArg (fun M : PresentModel one => M.graph.edge () ()) eq
    exact impossible.mpr trivial

theorem parallel_loss : oneEdge.relation = twoEdges.relation ∧ oneEdge ≠ twoEdges := by
  constructor
  · change (⟨_⟩ : RelGraph Unit) = ⟨_⟩
    congr 1
    funext a b
    cases a; cases b
    apply propext
    exact ⟨fun _ => ⟨false, trivial, rfl, rfl⟩, fun _ => ⟨false, rfl, rfl, rfl⟩⟩
  · intro eq
    have same := congrArg (fun M : Incidence.Model parallel => true ∈ M.edges) eq
    have bad : (true : Bool) = false := same.mpr trivial
    cases bad

theorem incomplete_loss : unknownEdge.relation = noEdge.relation ∧
    ¬ unknownEdge.Complete ∧ ¬ Incidence.Sat unknownEdge (.sourceKnown ()) := by
  refine ⟨?_, ?_, ?_⟩
  · change (⟨_⟩ : RelGraph Unit) = ⟨_⟩
    congr 1; funext a b; apply propext
    simp [unknownEdge, noEdge, incomplete]
  · intro h
    exact Bool.noConfusion (h () trivial).1
  · exact Bool.noConfusion

def cross_base_iso : Iso namedGraph indexedGraph := by
  let e : Bool ≃ Fin 2 :=
    { toFun := fun b => if b then 1 else 0
      invFun := fun n => n = 1
      left_inv := by intro b; cases b <;> rfl
      right_inv := by
        intro ⟨n, hn⟩
        match n with
        | 0 => rfl
        | 1 => rfl
        | n + 2 => omega }
  refine ⟨e, ?_⟩
  intro a b
  cases a <;> cases b <;> simp [namedGraph, indexedGraph, e]

end Silmaril.Logic.Graph.Examples.Proofs
