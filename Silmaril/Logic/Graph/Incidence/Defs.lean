module

public import Silmaril.Logic.Graph.Defs

/-! # Edge/node signatures with optional incidence

Edge identities retain parallel edges. Incidence is part of the signature;
renamings commute with it, including unknown endpoints. Models choose which
nodes/edges are present. Unknown is not an empty endpoint set. Total incidence
embeds by `some`; forgetting identities to a relation loses multiplicity and
forgets incomplete edges, so no unconditional reduct equivalence is claimed.
-/

@[expose] public section
namespace Silmaril.Logic.Graph.Incidence
open CategoryTheory Silmaril.Logic.Institution

structure Signature where
  Node : Type
  Edge : Type
  source : Edge → Option Node
  target : Edge → Option Node

@[ext] structure Hom (A B : Signature) where
  node : A.Node → B.Node
  edge : A.Edge → B.Edge
  source : ∀ e, (A.source e).map node = B.source (edge e)
  target : ∀ e, (A.target e).map node = B.target (edge e)

def Hom.id (A : Signature) : Hom A A :=
  ⟨_root_.id, _root_.id, fun _ => by simp, fun _ => by simp⟩
def Hom.comp {A B C : Signature} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨g.node ∘ f.node, g.edge ∘ f.edge,
    fun e => by simp only [← Option.map_map, f.source, g.source, Function.comp_apply],
    fun e => by simp only [← Option.map_map, f.target, g.target, Function.comp_apply]⟩

instance : Category Signature where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc f g h := rfl

structure TotalSignature where
  Node : Type
  Edge : Type
  source : Edge → Node
  target : Edge → Node

def TotalSignature.toOptional (A : TotalSignature) : Signature :=
  ⟨A.Node, A.Edge, some ∘ A.source, some ∘ A.target⟩

structure Model (A : Signature) where
  nodes : Set A.Node
  edges : Set A.Edge

/-- Known endpoints must be present. This does not assert unknown endpoints
are absent; require `Complete` to rule out incomplete present edges. -/
def Model.WellFormed {A : Signature} (M : Model A) : Prop :=
  ∀ e ∈ M.edges, ∀ n, A.source e = some n ∨ A.target e = some n → n ∈ M.nodes

def Model.Complete {A : Signature} (M : Model A) : Prop :=
  ∀ e ∈ M.edges, (A.source e).isSome ∧ (A.target e).isSome

inductive Sentence (A : Signature) where
  | node (n : A.Node)
  | edge (e : A.Edge)
  | sourceKnown (e : A.Edge)
  | targetKnown (e : A.Edge)

def sentenceMap {A B : Signature} (f : A ⟶ B) : Sentence A → Sentence B
  | .node n => .node (f.node n)
  | .edge e => .edge (f.edge e)
  | .sourceKnown e => .sourceKnown (f.edge e)
  | .targetKnown e => .targetKnown (f.edge e)

def Sat {A : Signature} (M : Model A) : Sentence A → Prop
  | .node n => n ∈ M.nodes
  | .edge e => e ∈ M.edges
  | .sourceKnown e => (A.source e).isSome
  | .targetKnown e => (A.target e).isSome

def reduct {A B : Signature} (f : A ⟶ B) (M : Model B) : Model A :=
  ⟨f.node ⁻¹' M.nodes, f.edge ⁻¹' M.edges⟩

def Model.relation {A : Signature} (M : Model A) : Silmaril.Semantics.Graph.RelGraph A.Node :=
  ⟨fun a b => ∃ e ∈ M.edges, A.source e = some a ∧ A.target e = some b⟩

end Silmaril.Logic.Graph.Incidence
