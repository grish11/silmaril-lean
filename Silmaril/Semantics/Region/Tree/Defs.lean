module

public import Silmaril.Semantics.Region.Abstract.Defs
public import Mathlib.Logic.Relation

/-! Abstract tree-indexed judgments. Parent links are proposed tree data, never
successor edges. Structural and dominance certificates are separate from Region.
No CFG, execution, finiteness or decidable equality is required. -/

@[expose] public section
namespace Silmaril.Semantics.Region.Tree
universe u v w x y

/-- Immediate parent data. `Rooted` separately certifies a rooted tree. -/
structure Shape (Vertex : Type u) where
  root : Vertex
  parent : Vertex → Option Vertex

def Shape.Child {V : Type u} (s : Shape V) (p c : V) : Prop := s.parent c = some p
/-- Reflexive descendants, including the node itself. -/
def Shape.Descendant {V : Type u} (s : Shape V) : V → V → Prop := Relation.ReflTransGen s.Child
/-- Every vertex has a finite parent chain to the distinguished root. -/
def Shape.Rooted {V : Type u} (s : Shape V) : Prop :=
  s.parent s.root = none ∧ ∀ v, s.Descendant s.root v

/-- Label leaves are explicit program points, not implicit exits. -/
inductive NodeData (Seg : Type u) (Lab : Type v) (Ann : Type w) where
  | segment (support : Seg) (annotation : Ann)
  | label (value : Lab)

structure AnnotatedTree (V : Type u) (Seg : Type v) (Lab : Type w) (Ann : Type x) where
  shape : Shape V
  data : V → NodeData Seg Lab Ann

abbrev SegTree (V : Type u) (Seg : Type v) (Lab : Type w) := AnnotatedTree V Seg Lab (Option Lab)
abbrev FullTree (V : Type u) (Seg : Type v) (Lab : Type w) := AnnotatedTree V Seg Lab Lab
abbrev BareTree (V : Type u) (Seg : Type v) (Lab : Type w) := AnnotatedTree V Seg Lab Unit
abbrev LabTree (V : Type u) (Lab : Type v) := SegTree V Unit Lab

/-- Structural terminal-leaf policy. It says nothing about outgoing CFG edges. -/
def AnnotatedTree.TerminalLeaves {V Seg Lab Ann} (t : AnnotatedTree V Seg Lab Ann) : Prop :=
  ∀ v l, t.data v = .label l → ∀ c, ¬ t.shape.Child v c

/-- Strict label-leaf profile, optional even as a structural requirement. -/
def AnnotatedTree.CompleteLeaves {V Seg Lab Ann} (t : AnnotatedTree V Seg Lab Ann) : Prop :=
  ∀ v, (∀ c, ¬ t.shape.Child v c) → ∃ l, t.data v = .label l

abbrev LabelLeafTree (V : Type u) (Seg : Type v) (Lab : Type w) :=
  {t : SegTree V Seg Lab // t.shape.Rooted ∧ t.TerminalLeaves ∧ t.CompleteLeaves}

def NodeData.mapAnn {Seg Lab A B} (f : A → B) : NodeData Seg Lab A → NodeData Seg Lab B
  | .segment s a => .segment s (f a)
  | .label l => .label l

def AnnotatedTree.mapAnn {V Seg Lab A B} (f : A → B) (t : AnnotatedTree V Seg Lab A) :
    AnnotatedTree V Seg Lab B := ⟨t.shape, fun v => (t.data v).mapAnn f⟩

def embedFull {V Seg Lab} : FullTree V Seg Lab → SegTree V Seg Lab := AnnotatedTree.mapAnn some

def eraseAnnotations {V Seg Lab} : SegTree V Seg Lab → BareTree V Seg Lab :=
  AnnotatedTree.mapAnn (fun _ => ())

/-- A completion must justify every segment annotation; there is no default label. -/
def FullyAnnotated {V Seg Lab} (t : SegTree V Seg Lab) : Prop :=
  ∀ v s a, t.data v = .segment s a → ∃ l, a = some l

noncomputable def complete {V Seg Lab} (t : SegTree V Seg Lab) (h : FullyAnnotated t) : FullTree V Seg Lab :=
  ⟨t.shape, fun v => match eq : t.data v with
    | .label l => .label l
    | .segment s a => .segment s (Classical.choose (h v s a eq))⟩

/-- Boundary is independent of all internal/leaf annotations. Exits may use any
carrier; the set profile below imposes no order on them. -/
structure Boundary (Body : Type u) (Lab : Type v) (Exits : Type w) where
  entry : Lab
  exits : Exits
  body : Body

def Boundary.map {A B Lab Exits} (f : A → B) (r : Boundary A Lab Exits) : Boundary B Lab Exits :=
  ⟨r.entry, r.exits, f r.body⟩

abbrev TreeRow (V : Type u) (Seg : Type v) (Lab : Type w) := Boundary (SegTree V Seg Lab) Lab (Set Lab)
abbrev FullRow (V : Type u) (Seg : Type v) (Lab : Type w) := Boundary (FullTree V Seg Lab) Lab (Set Lab)
abbrev RootOnlyRow (V : Type u) (Seg : Type v) (Lab : Type w) := Boundary (BareTree V Seg Lab) Lab (Set Lab)

/-- Root-only convention: the root segment receives the external entry label;
other segments are unlabeled. Explicit label leaves are retained unchanged. -/
noncomputable def embedRootOnly {V Seg Lab} (r : RootOnlyRow V Seg Lab) : TreeRow V Seg Lab := by
  classical
  exact ⟨r.entry, r.exits, ⟨r.body.shape, fun v => match r.body.data v with
    | .label l => .label l
    | .segment s _ => .segment s (if v = r.body.shape.root then some r.entry else none)⟩⟩

def eraseRootOnly {V Seg Lab} (r : TreeRow V Seg Lab) : RootOnlyRow V Seg Lab := r.map eraseAnnotations

def SegTree.labelAt {V Seg Lab} (t : SegTree V Seg Lab) (v : V) : Option Lab :=
  match t.data v with
  | .label l => some l
  | .segment _ a => a

def SegTree.labels {V Seg Lab} (t : SegTree V Seg Lab) : Set Lab := {l | ∃ v, t.labelAt v = some l}
def SegTree.leafLabels {V Seg Lab} (t : SegTree V Seg Lab) : Set Lab := {l | ∃ v, t.data v = .label l}
def SegTree.entryLabels {V Seg Lab} (t : SegTree V Seg Lab) : Set Lab :=
  {l | ∃ v s, t.data v = .segment s (some l)}

/-- Payload erasure preserves optional labels and label leaves, not segments. -/
def SegTree.toLabTree {V Seg Lab} (t : SegTree V Seg Lab) : LabTree V Lab :=
  ⟨t.shape, fun v => match t.data v with
    | .label l => .label l
    | .segment _ a => .segment () a⟩

/-- Sparse labels project to a forest of labeled frontiers. An edge crosses
one parent step, or an unlabeled intermediate vertex. No label is invented.
The root set can be empty or have several labels. -/
inductive Frontier {V Seg Lab} (t : SegTree V Seg Lab) : V → V → Prop
  | child {p c} : t.shape.Child p c → Frontier t p c
  | through {p m c} : Frontier t p m → t.labelAt m = none → t.shape.Child m c → Frontier t p c

structure LabelForest (Lab : Type u) where
  labels : Set Lab
  roots : Set Lab
  child : Lab → Lab → Prop

def SegTree.frontier {V Seg Lab} (t : SegTree V Seg Lab) : LabelForest Lab where
  labels := t.labels
  roots := {l | ∃ v, t.labelAt v = some l ∧
    (v = t.shape.root ∨ (t.labelAt t.shape.root = none ∧ Frontier t t.shape.root v))}
  child a b := ∃ p c, t.labelAt p = some a ∧ t.labelAt c = some b ∧ Frontier t p c

/-- Explicit roles do not identify an internal annotation with an exit allowance. -/
inductive LabelRole (Lab : Type u) where
  | internal (l : Lab)
  | exit (l : Lab)

def TreeRow.roleLabels {V Seg Lab} (r : TreeRow V Seg Lab) : Set (LabelRole Lab) :=
  LabelRole.internal '' r.body.labels ∪ LabelRole.exit '' r.exits

structure FlatRegion (Seg : Type u) (Lab : Type v) where
  entry : Lab
  support : Set Seg
  exits : Set Lab

abbrev LabelBoundary (Lab : Type u) := Boundary Unit Lab (Set Lab)

def FlatRegion.boundary {Seg Lab} (r : FlatRegion Seg Lab) : LabelBoundary Lab := ⟨r.entry, r.exits, ()⟩

/-- Generalized payloads may be whole (otherwise uninterpreted) regions. -/
structure RegionPiece (Support : Type u) (Lab : Type v) where
  entry : Lab
  support : Support
  exits : Set Lab

def pieceTree {V Support Lab} (shape : Shape V) (pieces : V → RegionPiece Support Lab) :
    SegTree V (RegionPiece Support Lab) Lab :=
  ⟨shape, fun v => .segment (pieces v) (some (pieces v).entry)⟩

/-- Interpret payload support explicitly, including collections of segments.
No operation on the abstract payload carrier is built into Region. -/
def TreeRow.flattenWith {V Payload Seg Lab} (elements : Payload → Set Seg)
    (r : TreeRow V Payload Lab) : FlatRegion Seg Lab where
  entry := r.entry
  exits := r.exits
  support := {s | ∃ v p a, r.body.data v = .segment p a ∧ s ∈ elements p}

def TreeRow.flatten {V Seg Lab} (r : TreeRow V Seg Lab) : FlatRegion Seg Lab := r.flattenWith Set.singleton

def TreeRow.boundary {V Seg Lab} (r : TreeRow V Seg Lab) : LabelBoundary Lab := ⟨r.entry, r.exits, ()⟩

/-- Primitive Region(context, tree). The payload can be any proposed tree,
without a CFG, structural certificate, or semantic interpretation. -/
abbrev RegionModel (Context : Type u) (Tree : Type v) := Abstract.RawModel (Context × Tree)
abbrev RegionPred (Img : Type u) (Assum : Type v) (Tree : Type w) := Img → Assum → Tree → Prop
abbrev ContextRegionPred (Context : Type u) (Tree : Type v) := Context → Tree → Prop
abbrev LawfulRegionModel {Context : Type u} {Tree : Type v} (rules : Abstract.Rules (Context × Tree)) :=
  Abstract.ClosedModel rules

def RegionModel.Holds {Context Tree} (M : RegionModel Context Tree) (c : Context) (t : Tree) : Prop := (c, t) ∈ M

def curry {Img Assum Tree} (M : RegionModel (Img × Assum) Tree) : RegionPred Img Assum Tree :=
  fun i a t => M.Holds (i, a) t

def uncurry {Img Assum Tree} (P : RegionPred Img Assum Tree) : RegionModel (Img × Assum) Tree :=
  {j | P j.1.1 j.1.2 j.2}

/-- The same positive rules presented on split-context predicates. `uncurry`
is only the atom representation equivalence, not an extraction helper. -/
structure CurriedLawfulModel {Img : Type u} {Assum : Type v} {Tree : Type w}
    (rules : Abstract.Rules ((Img × Assum) × Tree)) where
  val : RegionPred Img Assum Tree
  property : Abstract.Closed rules (uncurry val)

def image {Context A B} (f : A → B) (M : RegionModel Context A) : RegionModel Context B :=
  Abstract.forget (fun j => (j.1, f j.2)) M

/-- Independently specified flat predicates require a refinement proof. -/
def Refines {Context A B} (f : A → B) (M : RegionModel Context A) (N : RegionModel Context B) : Prop :=
  ∀ c t, M.Holds c t → N.Holds c (f t)

def HasWitnesses {Context A B} (f : A → B) (M : RegionModel Context A) (N : RegionModel Context B) : Prop :=
  ∀ c r, N.Holds c r → ∃ t, M.Holds c t ∧ f t = r

end Silmaril.Semantics.Region.Tree
