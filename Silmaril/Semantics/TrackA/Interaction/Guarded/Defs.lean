module

public import Silmaril.Semantics.TrackA.Interaction.Defs

/-! # Context-indexed guarded interaction

This first-order fragment equips each context with a signature. Each response
determines the context of its continuation. Recursive unfolding always takes
one layer. See the project guide for the relation to guarded interaction trees.
-/

@[expose] public section

namespace Silmaril.Semantics.TrackA.Interaction.Guarded

universe u v w x y z s i

structure Protocol (World : Type u) where
  effects : World → Signature.{v,w}
  advance (world : World) (q : (effects world).Request) : (effects world).Response q → World

variable {World : Type u} (P : Protocol.{u,v,w} World)

/-- The context travels with each completed exchange after forgetting the state
index. Different contexts can offer different requests with different replies. -/
def Protocol.signature : Signature where
  Request := Σ world : World, (P.effects world).Request
  Response q := (P.effects q.1).Response q.2

inductive Node (B : Signature.{x,y}) (A : Type z) (X : World → Type s) (world : World) where
  | ret (value : A)
  | tau (next : X world)
  | vis (q : (P.effects world).Request)
      (next : (reply : (P.effects world).Response q) → X (P.advance world q reply))
  | branch (kind : ChoiceKind) (shape : B.Request) (next : B.Response shape → X world)

/-- Forget the index of each state by retaining it as data in a dependent sum. -/
def Node.erase {B : Signature.{x,y}} {A : Type z} {X : World → Type s} {world : World} :
    Node P B A X world → Interaction.Node P.signature B A (Sigma X)
  | .ret value => .ret value
  | .tau next => .tau ⟨world, next⟩
  | .vis q next => .vis ⟨world, q⟩ (fun r => ⟨P.advance world q r, next r⟩)
  | .branch kind shape next => .branch kind shape (fun b => ⟨world, next b⟩)

structure Forest (B : Signature.{x,y}) (A : Type z) (I : Type i) where
  State : World → Type s
  unfold {world : World} : State world → Node P B A State world
  entry : I → World
  root (i : I) : State (entry i)

/-- A rooted first-order guarded interaction tree. -/
abbrev GITree (B : Signature.{x,y}) (A : Type z) := Forest P B A Unit

def Forest.erase {B : Signature.{x,y}} {A : Type z} {I : Type i} (forest : Forest P B A I) :
    Interaction.Forest P.signature B A I where
  State := Sigma forest.State
  unfold x := Node.erase P (forest.unfold x.2)
  root i := ⟨forest.entry i, forest.root i⟩

end Silmaril.Semantics.TrackA.Interaction.Guarded
