module

public import Silmaril.Semantics.Graph.Defs
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # The directed relational graph institution

Node names are signatures, edge claims are atomic sentences, relations are
models. Arbitrary renamings use inverse-image reducts: satisfaction is iff,
not the one-way truth condition of a graph homomorphism. Edges include loops;
parallel identities and explicit vertex presence require separate variants.
-/

@[expose] public section
namespace Silmaril.Logic.Graph
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Semantics.Graph

structure Signature where
  Node : Type

@[ext] structure Signature.Hom (A B : Signature) where
  node : A.Node → B.Node

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨id⟩
  comp f g := ⟨g.node ∘ f.node⟩

abbrev Sentence (A : Signature) := A.Node × A.Node
abbrev Model (A : Signature) := RelGraph A.Node

def sentenceMap {A B : Signature} (f : A ⟶ B) (p : Sentence A) : Sentence B := (f.node p.1, f.node p.2)
def reduct {A B : Signature} (f : A ⟶ B) (M : Model B) : Model A := ⟨fun a b => M.edge (f.node a) (f.node b)⟩
def Sat {A : Signature} (M : Model A) (p : Sentence A) : Prop := M.edge p.1 p.2

def room (A : Signature) : Room.{0,0,0} :=
  ⟨Sentence A, Cat.of (Discrete (Model A)), fun M p => Sat (Discrete.as M) p⟩
def corridor {A B : Signature} (f : A ⟶ B) : room A ⟶ room B :=
  ⟨sentenceMap f, Discrete.functor fun M => Discrete.mk (reduct f M), fun _ _ => Iff.rfl⟩

/-- Explicit presence, independent of genuine self-loops. -/
structure PresentModel (A : Signature) where
  present : Set A.Node
  graph : Model A

def PresentModel.WellFormed {A : Signature} (M : PresentModel A) : Prop :=
  ∀ a b, M.graph.edge a b → a ∈ M.present ∧ b ∈ M.present

def presentReduct {A B : Signature} (f : A ⟶ B) (M : PresentModel B) : PresentModel A :=
  ⟨f.node ⁻¹' M.present, reduct f M.graph⟩

inductive PresentSentence (A : Signature) where
  | node (a : A.Node)
  | edge (a b : A.Node)

def presentMap {A B : Signature} (f : A ⟶ B) : PresentSentence A → PresentSentence B
  | .node a => .node (f.node a)
  | .edge a b => .edge (f.node a) (f.node b)
def PresentSat {A : Signature} (M : PresentModel A) : PresentSentence A → Prop
  | .node a => a ∈ M.present
  | .edge a b => M.graph.edge a b

def presentRoom (A : Signature) : Room.{0,0,0} :=
  ⟨PresentSentence A, Cat.of (Discrete (PresentModel A)), fun M p => PresentSat (Discrete.as M) p⟩
def presentCorridor {A B : Signature} (f : A ⟶ B) : presentRoom A ⟶ presentRoom B :=
  ⟨presentMap f, Discrete.functor fun M => Discrete.mk (presentReduct f M), fun _ p => by cases p <;> rfl⟩

/-- Loop-as-presence encoding. Genuine diagonal edges are deliberately lost.
Off-diagonal edges remain real edges. Its naturality needs injective renaming. -/
def markPresence {A : Signature} (M : PresentModel A) : Model A :=
  ⟨fun a b => (a = b ∧ a ∈ M.present) ∨ (a ≠ b ∧ M.graph.edge a b)⟩

end Silmaril.Logic.Graph
