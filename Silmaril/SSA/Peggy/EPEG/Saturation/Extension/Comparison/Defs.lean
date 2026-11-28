module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.ZeroSample
public import Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.Defs
public import Mathlib.Logic.Embedding.Basic

/-! # Comparing independently extended typed E-PEGs -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension

open PEG
open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n k j l : Nat}

/-- An address injection with a sort proof at each mapped vertex. -/
structure VertexMap (source : Fin n → Ty Data) (target : Fin k → Ty Data) where
  address : Fin n ↪ Fin k
  sort_eq : ∀ i, target (address i) = source i

namespace VertexMap

variable {a : Fin n → Ty Data} {b : Fin k → Ty Data} {c : Fin j → Ty Data}

def ref (f : VertexMap a b) {t : Ty Data} (r : Ref a t) : Ref b t :=
  ⟨f.address r.id, (f.sort_eq r.id).trans r.typed⟩

def tuple (f : VertexMap a b) {ts : List (Ty Data)} (args : Tuple (Ref a) ts) :
    Tuple (Ref b) ts :=
  args.map fun _ => f.ref

def node (f : VertexMap a b) {t : Ty Data} (row : Node P params (Fin l) a t) :
    Node P params (Fin l) b t :=
  Node.ofLabel row.label (f.tuple row.args)

def identity (a : Fin n → Ty Data) : VertexMap a a :=
  ⟨Function.Embedding.refl _, fun _ => rfl⟩

def comp (g : VertexMap b c) (f : VertexMap a b) : VertexMap a c :=
  ⟨f.address.trans g.address, fun i => (g.sort_eq (f.address i)).trans (f.sort_eq i)⟩

theorem node_heq (f : VertexMap a b) {t t' : Ty Data} (sorts : t = t')
    {lhs : Node P params (Fin l) a t} {rhs : Node P params (Fin l) a t'} (eq : HEq lhs rhs) :
    HEq (f.node lhs) (f.node rhs) := by
  subst t'
  rw [eq_of_heq eq]

end VertexMap

def Row.vertices {g : Graph P params results n l} (row : Row g) : VertexMap g.sort row.sort :=
  ⟨⟨Fin.castSucc, fun _ _ h => Fin.castSucc_inj.mp h⟩, row.sort_old⟩

/-- The source is a closed subtable of the target up to an address injection.
Labels, loop coordinates, ordered ports and the ordered boundary are preserved.
Only source same-class pairs must remain joined. -/
structure Embedding (source : State P params results n l) (target : State P params results k l) where
  vertices : VertexMap source.graph.sort target.graph.sort
  rows : ∀ i, HEq (target.graph.node (vertices.address i)) (vertices.node (source.graph.node i))
  roots : target.graph.roots = vertices.tuple source.graph.roots
  forest : target.graph.forest = source.graph.forest
  classes : ∀ a b, source.classes a = source.classes b →
    target.classes (vertices.address a) = target.classes (vertices.address b)

variable {small : State P params results n l} {large : State P params results k l}

theorem Embedding.hasNode (e : Embedding small large) {t : Ty Data} {ts : List (Ty Data)}
    {r : Ref small.graph.sort t} {label : Label P params (Fin l) ts t}
    {args : Tuple (Ref small.graph.sort) ts} (shape : Rules.HasNode r label args) :
    Rules.HasNode (g := large.graph) (e.vertices.ref r) label (e.vertices.tuple args) :=
  (e.rows r.id).trans (e.vertices.node_heq r.typed shape)

namespace ZeroSample

def ofNodes {g : Graph P params results n l} {t : Ty Data} {zero : P [] .count} (loop : Fin l)
    (site theta initial feedback : Ref g.sort t) (count : Ref g.sort .count)
    (evalNode : Rules.HasNode site (.eval loop) (.cons theta (.cons count .nil)))
    (thetaNode : Rules.HasNode theta (.theta loop) (.cons initial (.cons feedback .nil)))
    (countNode : Rules.HasNode count (.op zero) .nil) : ZeroSample g site.id zero := by
  obtain ⟨i, eq⟩ := site
  subst t
  exact ⟨loop, theta, initial, feedback, count, evalNode, thetaNode, countNode⟩

/-- Transport the actual matched rows and their ordered operands. -/
def transport {site : Fin n} {zero : P [] .count} (found : ZeroSample small.graph site zero)
    (e : Embedding small large) : ZeroSample large.graph (e.vertices.address site) zero :=
  ofNodes found.loop (e.vertices.ref (Ref.ofId small.graph.sort site))
    (e.vertices.ref found.theta) (e.vertices.ref found.initial) (e.vertices.ref found.feedback)
    (e.vertices.ref found.count) (e.hasNode found.evalNode) (e.hasNode found.thetaNode)
    (e.hasNode found.countNode)

end ZeroSample

def Embedding.mapRow (e : Embedding small large) (row : Row small.graph) : Row large.graph :=
  ⟨row.inputs, row.out, row.label, e.vertices.tuple row.args⟩

/-- Map old addresses through the original injection and the fresh row to
the fresh row of the other append. In particular, existing target rows
are never used as the image of the new source row. -/
def Embedding.appendVertices (e : Embedding small large) (row : Row small.graph) :
    VertexMap row.sort (e.mapRow row).sort where
  address :=
    ⟨Fin.lastCases (Fin.last k) (fun i => (e.vertices.address i).castSucc), by
      intro a b h
      induction a using Fin.lastCases <;> induction b using Fin.lastCases
      · rfl
      · simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
        exact (Nat.ne_of_lt (e.vertices.address _).isLt (congrArg Fin.val h).symm).elim
      · simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
        exact (Nat.ne_of_lt (e.vertices.address _).isLt (congrArg Fin.val h)).elim
      · apply congrArg Fin.castSucc
        exact e.vertices.address.injective (Fin.castSucc_inj.mp (by simpa using h))⟩
  sort_eq := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [Embedding.mapRow]
    | cast i => simpa using e.vertices.sort_eq i

/-- Existence of an embedding is a preorder on packaged states. -/
def Comparable (source target : Output P params results l) : Prop :=
  Nonempty (Embedding source.2 target.2)

abbrev Analysis (P : InstructionSet.{u,v} Data) (params results : List (Ty Data)) (l : Nat) :=
  NormalForms.Analysis (Output P params results l)

def Inflationary (analysis : Analysis P params results l) : Prop :=
  NormalForms.Inflationary Comparable analysis

/-- Equation (4.2) for the embedding comparison. -/
def MonotoneAnalysis (analysis : Analysis P params results l) : Prop :=
  NormalForms.MonotoneSimulation Comparable analysis

/-- One successful zero-sample generation at any witnessed site. Each
transition is precisely the existing fresh-append, one-merge-fuel step.
Identity choices are allowed separately, as in §4. -/
def ZeroSampleAnalysis (zero : P [] .count) : Analysis P params results l :=
  fun source target => target = source ∨
    ∃ (site : Fin source.1) (found : ZeroSample source.2.graph site zero),
      target = ⟨_, found.step.apply⟩

abbrev ZeroSampleFamily (zero : P [] .count) : NormalForms.Family (Output P params results l) Unit :=
  fun _ => ZeroSampleAnalysis zero

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension
