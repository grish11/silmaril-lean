module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Certificate

import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Traversal

/-! # Reachability and certificate exactness of guarded product search -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open Syntax (Payload)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
/-- Explore exactly the reachable packet pairs for the supplied edge function. -/
theorem ProductSearch.visits_exact (edges : ProductConfig R T → List (ProductEdge S R T))
    (entry : ProductConfig R T) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    let seen := ProductSearch.visits edges entry left right
    (seen.map Prod.fst).Nodup ∧
      ∀ p, p ∈ seen.map Prod.fst ↔ ∃ trail, ProductPath edges entry trail p :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.product_visits_exact
    edges entry left right

/-- Each stored trail witnesses the recorded visit. -/
theorem ProductSearch.visits_path {edges : ProductConfig R T → List (ProductEdge S R T)}
    {entry : ProductConfig R T} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
    {visit : ProductSearch.Visit S R T} (listed : visit ∈ ProductSearch.visits edges entry left right) :
    ProductPath edges entry visit.2 visit.1 :=
  (Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.product_visits_spec
    edges entry left right).2.1 visit listed

/-- A simple visiting path needs at most one state per reachable pair. -/
theorem ProductSearch.simple_path_bound
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    {edges : ProductConfig R T → List (ProductEdge S R T)}
    {start point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath edges start trail point) (simple : (ProductPath.vertices start trail).Nodup) :
    trail.length + 1 ≤ (ProductSearch.visits edges start left right).length :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.product_simple_path_bound
    left right walk simple

theorem Head.checkPair_edges [DecidableEq Φ] (replies : ReplyEnumeration S)
    (rel : Packet R → Packet T → Bool) (p : Head S R) (q : Head S T) :
    p.checkPair replies rel q =
      (p.checkPair replies (fun _ _ => true) q &&
        (p.productEdges replies q).all fun edge => rel edge.2.1 edge.2.2) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.check_pair_edges
    replies rel p q

theorem Head.product_edge_forms [DecidableEq Φ] (replies : ReplyEnumeration S)
    {lower : Head S R} {upper : Head S T} {edge : ProductEdge S R T}
    (listed : edge ∈ lower.productEdges replies upper) :
    ∃ (f : Φ) (arg : Payload (instrSrc f))
      (next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R)
      (next' : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T)
      (reply : Packet (S.replies f)),
      lower = .request f arg next ∧ upper = .request f arg next' ∧
      edge = (⟨f, reply⟩, next reply.1 reply.2, next' reply.1 reply.2) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.head_edge_forms
    replies listed

section Paths

variable {edges : ProductConfig R T → List (ProductEdge S R T)}
  {start point : ProductConfig R T} {trail : List (ProductEdge S R T)}

theorem ProductPath.nil_end (walk : ProductPath edges start [] point) : start = point :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.path_nil walk

theorem ProductPath.uncons {edge : ProductEdge S R T}
    (walk : ProductPath edges start (edge :: trail) point) :
    edge ∈ edges start ∧ ProductPath edges edge.2 trail point :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.path_uncons walk

/-- A shortest path to a fixed pair cannot revisit a pair. -/
theorem ProductPath.shortest (walk : ProductPath edges start trail point) :
    ∃ shortest, ProductPath edges start shortest point ∧
      (ProductPath.vertices start shortest).Nodup ∧
      ∀ other, ProductPath edges start other point → shortest.length ≤ other.length :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.path_shortest walk

theorem ProductPath.covered (walk : ProductPath edges start trail point) (domain : List (ProductConfig R T))
    (initial : start ∈ domain)
    (closed : ∀ p ∈ domain, ∀ edge ∈ edges p, edge.2 ∈ domain) :
    point ∈ domain ∧ ProductPath.vertices start trail ⊆ domain :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.path_covered walk domain initial closed

variable [DecidableEq Φ]

theorem Table.product_edge_forms {g : Table S R} {h : Table S T}
    {caller : Payload (R.get g.entry)} {caller' : Payload (T.get h.entry)} (replies : ReplyEnumeration S)
    {p : ProductConfig R T} {edge : ProductEdge S R T}
    (listed : edge ∈ g.productEdges h caller caller' replies p) :
    ∃ (f : Φ) (arg : Payload (instrSrc f))
      (next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R)
      (next' : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T)
      (reply : Packet (S.replies f)),
      g.head caller p.1 = .request f arg next ∧ h.head caller' p.2 = .request f arg next' ∧
      edge = (⟨f, reply⟩, next reply.1 reply.2, next' reply.1 reply.2) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.edge_forms replies listed

end Paths

variable [DecidableEq Φ]

variable (g : Table S R) (h : Table S T)
  (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
  (replies : ReplyEnumeration S)

/-- The computed visits count exactly the distinct reachable typed pairs. -/
theorem Table.productVisits_exact (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    let entry : ProductConfig R T := (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
    let edges := g.productEdges h caller caller' replies
    let seen := g.productVisits h caller caller' replies left right
    (seen.map Prod.fst).Nodup ∧
      ∀ p, p ∈ seen.map Prod.fst ↔ ∃ trail, ProductPath edges entry trail p :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.visits_exact
    g h caller caller' replies left right

/-- A successful search returns a closed certificate of reachable pairs.
A mismatch has a typed shared reply path and fails the local comparison. -/
theorem Table.searchProduct_correct (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    match g.searchProduct h caller caller' replies left right with
    | .accepted pairs => g.checkProduct h caller caller' replies pairs = true ∧
      ∀ pair ∈ pairs, ∃ path, ProductPath (g.productEdges h caller caller' replies)
        (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩) path pair
    | .mismatch pair path =>
      ProductPath (g.productEdges h caller caller' replies) (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩) path pair ∧
      g.productLocal h caller caller' replies pair = false :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.search_correct
    g h caller caller' replies left right

/-- Search succeeds exactly when a closed certificate containing the entry
is accepted by the existing checker. -/
theorem Table.searchProduct_accepts_iff (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    (∃ pairs, g.searchProduct h caller caller' replies left right = .accepted pairs) ↔
    ∃ pairs, g.checkProduct h caller caller' replies pairs = true :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.search_accepts_iff
    g h caller caller' replies left right

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
