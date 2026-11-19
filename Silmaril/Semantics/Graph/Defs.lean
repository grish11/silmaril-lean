module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Lattice.Disjoint

/-! # Relational graph views

Edges point from source to successor. Relational graphs allow genuine loops
and forget parallel-edge identities. Presence, roots and CFG boundaries are
separate observations, never encoded by a loop in this base representation.
-/

@[expose] public section
namespace Silmaril.Semantics.Graph
universe u v w

structure RelGraph (V : Type u) where
  edge : V → V → Prop

structure GraphLike (G : Type u) (V : Type v) where
  graph : G → RelGraph V

structure CFGLike (G : Type u) (V : Type v) extends GraphLike G V where
  entry : G → V
  internal : G → Set V
  exits : G → Set V

/-- Exact structural isomorphism, including all loops and cross edges. -/
structure Iso {V : Type u} {W : Type v} (g : RelGraph V) (h : RelGraph W) where
  vertices : V ≃ W
  edge_iff : ∀ a b, h.edge (vertices a) (vertices b) ↔ g.edge a b

def Iso.refl {V : Type u} (g : RelGraph V) : Iso g g := ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩
def Iso.trans {V : Type u} {W : Type v} {X : Type w} {g : RelGraph V} {h : RelGraph W}
    {k : RelGraph X} (f : Iso g h) (j : Iso h k) : Iso g k :=
  ⟨f.vertices.trans j.vertices, fun a b => (j.edge_iff _ _).trans (f.edge_iff a b)⟩

def RelGraph.undirected {V : Type u} (g : RelGraph V) : RelGraph V :=
  ⟨fun a b => a ≠ b ∧ (g.edge a b ∨ g.edge b a)⟩

/-- Explicit undirected-simple branch-set minor convention, even when input
relations were directed. Branch sets are nonempty, disjoint and connected by
paths staying inside the set; each source adjacency has an inter-set edge.
This is not a directed minor or an isomorphism. -/
structure Minor {V : Type u} {W : Type v} (small : RelGraph V) (large : RelGraph W) where
  branch : V → Set W
  nonempty : ∀ v, (branch v).Nonempty
  disjoint : ∀ a b, a ≠ b → Disjoint (branch a) (branch b)
  connected : ∀ v a, a ∈ branch v → ∀ b, b ∈ branch v →
    Relation.ReflTransGen (fun x y => x ∈ branch v ∧ y ∈ branch v ∧ large.undirected.edge x y) a b
  adjacency : ∀ a b, small.undirected.edge a b →
    ∃ x ∈ branch a, ∃ y ∈ branch b, large.undirected.edge x y

/-- A precise two-boundary compositional CFG grammar. Vertices are supplied
by the client, so freshness/disjointness must be certified separately. -/
inductive Structured (V : Type u) where
  | edge (entry exit : V)
  | sequence (left right : Structured V)
  | selection (entry exit : V) (yes no : Structured V)
  | iteration (header exit : V) (body : Structured V)

def Structured.entry {V : Type u} : Structured V → V
  | .edge a _ | .selection a _ _ _ | .iteration a _ _ => a
  | .sequence p _ => p.entry

def Structured.exit {V : Type u} : Structured V → V
  | .edge _ b | .selection _ b _ _ | .iteration _ b _ => b
  | .sequence _ q => q.exit

def Structured.graph {V : Type u} : Structured V → RelGraph V
  | .edge a b => ⟨fun x y => x = a ∧ y = b⟩
  | .sequence p q => ⟨fun x y => p.graph.edge x y ∨ q.graph.edge x y ∨ x = p.exit ∧ y = q.entry⟩
  | .selection a b p q => ⟨fun x y => p.graph.edge x y ∨ q.graph.edge x y ∨
      (x = a ∧ (y = p.entry ∨ y = q.entry)) ∨ ((x = p.exit ∨ x = q.exit) ∧ y = b)⟩
  | .iteration a b p => ⟨fun x y => p.graph.edge x y ∨
      (x = a ∧ (y = b ∨ y = p.entry)) ∨ (x = p.exit ∧ y = a)⟩

def Structured.nodes {V : Type u} : Structured V → Set V
  | .edge a b => {a, b}
  | .sequence p q => p.nodes ∪ q.nodes
  | .selection a b p q => {a, b} ∪ p.nodes ∪ q.nodes
  | .iteration a b p => {a, b} ∪ p.nodes

/-- Fresh boundaries and disjoint child vertex sets enforce compositional
shapes. Shared labels are not silently allowed to encode arbitrary graphs. -/
def Structured.WellFormed {V : Type u} : Structured V → Prop
  | .edge a b => a ≠ b
  | .sequence p q => p.WellFormed ∧ q.WellFormed ∧ Disjoint p.nodes q.nodes
  | .selection a b p q => a ≠ b ∧ p.WellFormed ∧ q.WellFormed ∧
      Disjoint p.nodes q.nodes ∧ a ∉ p.nodes ∪ q.nodes ∧ b ∉ p.nodes ∪ q.nodes
  | .iteration a b p => a ≠ b ∧ p.WellFormed ∧ a ∉ p.nodes ∧ b ∉ p.nodes

/-- Membership requires an actual isomorphism to a chosen grammar term.
No claim that arbitrary CFGs have such a witness. -/
def HasStructuredWitness {V : Type u} (g : RelGraph V) : Prop := ∃ p : Structured V, p.WellFormed ∧ Nonempty (Iso p.graph g)

end Silmaril.Semantics.Graph
