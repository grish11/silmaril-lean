module

public import Silmaril.Semantics.Region.Defs
public import Silmaril.Semantics.Region.Tree.CFG.Defs
public import Silmaril.Semantics.Graph.Defs
public import Silmaril.Semantics.Region.Semantic.Defs

/-! # Proof decorations and transport, outside the raw model lattice -/

@[expose] public section
namespace Silmaril.Semantics.Region.Certified
open Silmaril.Semantics.Graph
universe u v w z
variable {Img : Type u} {Intf : Type v} {Seg : Type w} {Lab : Type z}

abbrev Model := SegmentRegionModel Img Intf Seg Lab

/-- Pointwise positive implication on all five named judgment shapes. -/
abbrev Refines (M N : Model (Img := Img) (Intf := Intf) (Seg := Seg) (Lab := Lab)) : Prop :=
  M.toAtoms ⊆ N.toAtoms

structure BasicBlock (M : Model (Img := Img) (Intf := Intf) (Seg := Seg) (Lab := Lab))
    (image : Img) (iface : Intf) where
  segment : Seg
  entry : Lab
  exits : Finset Lab
  valid : M.BB image iface segment entry exits

/-- Region and graph certificates are separate, with explicit coherence.
A stated/unproved decomposition uses the same data without these proof fields. -/
structure WithGraph (M : Model (Img := Img) (Intf := Intf) (Seg := Seg) (Lab := Lab))
    (image : Img) (iface : Intf) (G : Type*) (graphValid : G → Prop)
    (coherent : SegmentRow Seg Lab → G → Prop) where
  row : SegmentRow Seg Lab
  graph : G
  region_valid : M.Reg image iface row.support row.entry row.exits
  graph_valid : graphValid graph
  agreement : coherent row graph

/-- Chosen support/label interpretation is independent of model membership. -/
def CFGCoherent (labels : Finset Seg → Set Lab) (r : SegmentRow Seg Lab) (g : Tree.FlatCFG Lab) : Prop :=
  g.entry = r.entry ∧ g.internal = labels r.support ∧ g.exits = {l | l ∈ r.exits}

abbrev WithCFG (M : Model (Img := Img) (Intf := Intf) (Seg := Seg) (Lab := Lab))
    (image : Img) (iface : Intf) (graphValid : Tree.FlatCFG Lab → Prop)
    (labels : Finset Seg → Set Lab) :=
  WithGraph M image iface (Tree.FlatCFG Lab) graphValid (CFGCoherent labels)

def BasicBlock.transport {M N : Model (Img := Img) (Intf := Intf) (Seg := Seg) (Lab := Lab)}
    (h : Refines M N) {image : Img} {iface : Intf} (b : BasicBlock M image iface) : BasicBlock N image iface :=
  ⟨b.segment, b.entry, b.exits, h (a := .bb image iface b.segment b.entry b.exits) b.valid⟩

def WithGraph.transport {M N : Model (Img := Img) (Intf := Intf) (Seg := Seg) (Lab := Lab)}
    (h : Refines M N) {image : Img} {iface : Intf} {G : Type*} {P Q : G → Prop}
    {coherent : SegmentRow Seg Lab → G → Prop} (graph : ∀ g, P g → Q g)
    (r : WithGraph M image iface G P coherent) : WithGraph N image iface G Q coherent :=
  ⟨r.row, r.graph, h (a := .reg image iface r.row.support r.row.entry r.row.exits) r.region_valid, graph r.graph r.graph_valid, r.agreement⟩

def cfgView : CFGLike (Tree.FlatCFG Lab) Lab :=
  ⟨⟨fun g => ⟨fun a b => b ∈ g.successors a⟩⟩, Tree.FlatCFG.entry, Tree.FlatCFG.internal, Tree.FlatCFG.exits⟩

/-- State-machine edges retain all states. PC projection below can identify
states and introduce graph paths with no single execution witness. -/
def stateView {S Ev Stop : Type*} {L : Type*} : GraphLike (TransitionSystem S L Ev Stop) S :=
  ⟨fun T => ⟨fun s t => ∃ es, T.step s es t⟩⟩
def labelGraph {S Ev Stop : Type*} (T : TransitionSystem S Lab Ev Stop) : RelGraph Lab :=
  ⟨fun a b => ∃ s es t, T.pc s = a ∧ T.pc t = b ∧ T.step s es t⟩

end Silmaril.Semantics.Region.Certified
