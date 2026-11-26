module

public import Silmaril.Semantics.ITree.Thms
public import Silmaril.Semantics.TrackA.Interaction.Defs

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interaction

universe u v

/-- The existing weak ITree's indexed-event representation of a signature. -/
inductive IndexedEvent (S : Signature.{u,u}) : Type u → Type u where
  | request (q : S.Request) : IndexedEvent S (S.Response q)

/-- Pack a family of events indexed by the response type as a signature. -/
def Signature.ofIndexed (E : Type u → Type v) : Signature where
  Request := Σ R : Type u, E R
  Response := Sigma.fst

abbrev WeakITree (S : Signature.{u,u}) (A : Type v) :=
  Silmaril.Elgot.ITree.Tree (IndexedEvent S) A

namespace WeakITree

open Silmaril.Elgot.ITree (out)

/-- A weak ITree has already erased finite tau steps. Its undefined weak
observation is a silent self-loop in the delayed representation. -/
noncomputable def unfold {S : Signature.{u,u}} {A : Type v} :
    Coalgebra S Signature.noChoice A (WeakITree S A) := fun tree => by
  classical
  exact if h : (out tree).Dom then
    match (out tree).get h with
    | .ret a => .ret a
    | .vis (.request q) next => .vis q next
  else .tau tree

noncomputable def toDelayed {S : Signature.{u,u}} {A : Type v} (tree : WeakITree S A) :
    ITree S A where
  State := WeakITree S A
  unfold := unfold
  root _ := tree

end WeakITree

end Silmaril.Semantics.TrackA.Interaction
