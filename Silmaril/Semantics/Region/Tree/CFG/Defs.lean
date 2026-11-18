module

public import Silmaril.Semantics.Region.Tree.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Tree
universe u v w x

/-- Independent flat labeled CFG data. Successors include loops, cross edges
and outward labels. `SourceClosed` can restrict adjacency to internal sources. -/
structure FlatCFG (Lab : Type u) where
  entry : Lab
  internal : Set Lab
  exits : Set Lab
  successors : Lab → Set Lab

def FlatCFG.SourceClosed {Lab} (g : FlatCFG Lab) : Prop :=
  ∀ a b, b ∈ g.successors a → a ∈ g.internal

/-- A CFG enriches a primitive region proposal with adjacency. Tree parent
links and outgoing successor labels are independent fields. -/
structure SegCFG (V : Type u) (Seg : Type v) (Lab : Type w) where
  region : TreeRow V Seg Lab
  successors : V → Set Lab

/-- Existentially union successors of all vertices with the same source label.
Unlabeled sources have no invented label; their adjacency is not exported. -/
def SegCFG.flatten {V Seg Lab} (g : SegCFG V Seg Lab) : FlatCFG Lab where
  entry := g.region.entry
  internal := g.region.body.labels
  exits := g.region.exits
  successors a := {b | ∃ v, g.region.body.labelAt v = some a ∧ b ∈ g.successors v}

/-- A sufficient coverage policy for lifting an independently supplied flat
CFG. This is observation coverage, not a dominance certificate. -/
structure LabelCover {V Seg Lab} (r : TreeRow V Seg Lab) (g : FlatCFG Lab) : Prop where
  entry_eq : r.entry = g.entry
  exits_eq : r.exits = g.exits
  labels_eq : r.body.labels = g.internal
  source_closed : g.SourceClosed

def SegCFG.lift {V Seg Lab} (r : TreeRow V Seg Lab) (g : FlatCFG Lab) : SegCFG V Seg Lab where
  region := r
  successors v := {b | ∃ a, r.body.labelAt v = some a ∧ b ∈ g.successors a}

def UniqueLabels {V Seg Lab} (t : SegTree V Seg Lab) : Prop :=
  ∀ v w l, t.labelAt v = some l → t.labelAt w = some l → v = w

/-- An actual graph is covered by a candidate overapproximation. This is an
additional obligation, never inferred from primitive region membership. -/
structure Covers {Lab} (candidate actual : FlatCFG Lab) : Prop where
  entry_eq : candidate.entry = actual.entry
  internal : actual.internal ⊆ candidate.internal
  exits : actual.exits ⊆ candidate.exits
  successors : ∀ a, a ∈ actual.internal → actual.successors a ⊆ candidate.successors a

/-- Candidate and actual adjacency agree on the declared actual sources. -/
def ExactOn {Lab} (candidate actual : FlatCFG Lab) : Prop :=
  ∀ a, a ∈ actual.internal → candidate.successors a = actual.successors a

/-- A proposed CFG enrichment admitted by an independently chosen primitive
region relation. This proof decoration is not part of the lattice subtype. -/
structure RegionCandidate {Context V Seg Lab} (M : RegionModel Context (TreeRow V Seg Lab)) (context : Context) where
  cfg : SegCFG V Seg Lab
  admitted : M.Holds context cfg.region

structure CoveredCandidate {Context V Seg Lab} (M : RegionModel Context (TreeRow V Seg Lab))
    (context : Context) (actual : FlatCFG Lab) extends RegionCandidate M context where
  coverage : Covers cfg.flatten actual

/-- Tree and flat CFG relation variants inherit the same powerset and
positive-rule closed lattices as primitive region relations. -/
abbrev TreeCFGModel (Context : Type u) (V : Type v) (Seg : Type w) (Lab : Type x) :=
  RegionModel Context (SegCFG V Seg Lab)
abbrev FlatCFGModel (Context : Type u) (Lab : Type v) := RegionModel Context (FlatCFG Lab)

def eraseCFG {Context V Seg Lab} (M : TreeCFGModel Context V Seg Lab) : FlatCFGModel Context Lab :=
  image SegCFG.flatten M

end Silmaril.Semantics.Region.Tree
