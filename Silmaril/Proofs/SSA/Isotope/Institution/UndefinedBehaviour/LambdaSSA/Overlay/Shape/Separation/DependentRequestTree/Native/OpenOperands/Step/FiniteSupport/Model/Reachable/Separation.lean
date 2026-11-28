module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Probe.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open Syntax (Payload Primitives StatePrimitives)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {g : Table S R} {h : Table S T} {a : Payload (R.get g.entry)} {b : Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}

theorem payload_path_refutes {A : Syntax.Ty} (g : Endpoint S R A) (h : Endpoint S T A)
    (a : Payload (R.get g.control.entry)) (b : Payload (T.get h.control.entry))
    {start point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.control.productEdges h.control a b replies) start trail point)
    (bad : ¬ (g.control.head a point.1).MatchesWith
      (fun i j => (g.returnPacket a point.1 i).raw = (h.returnPacket b point.2 j).raw)
      (fun _ _ => True) (h.control.head b point.2)) :
    ∃ prim : Primitives Φ (trail.length + 1),
      ¬ g.observeAt a prim start.1 0 ≤ h.observeAt b prim start.2 0 := by
  induction trail generalizing start with
  | nil =>
    have eq := walk.nil_end
    subst point
    exact g.local_mismatch_refutes h a b start.1 start.2 0 bad
  | cons edge trail ih =>
    obtain ⟨listed, rest⟩ := walk.uncons
    obtain ⟨f, arg, next, next', reply, lower, upper, edgeEq⟩ := Table.product_edge_forms replies listed
    obtain ⟨suffix, separates⟩ := ih rest
    rw [edgeEq] at separates
    exact g.prepend_refutation h a b start.1 start.2 lower upper reply suffix 0 separates

include left right in
theorem path_refutes {start point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies) start trail point)
    (bad : g.productLocal h a b replies point = false) :
    ∃ prim : Primitives Φ (trail.length + 1),
      ¬ g.observeAt a prim start.1 0 ≤ h.observeAt b prim start.2 0 := by
  have _ := left
  have _ := right
  obtain ⟨prim, fails⟩ := payload_path_refutes (Endpoint.unit g) (Endpoint.unit h) a b walk (by
    intro good
    have tags : (g.head a point.1).Matches (fun _ _ => True) (h.head b point.2) :=
      (Endpoint.unit_matches_iff g h a b point.1 point.2 _ _ _).mp good
    have check := (Head.checkPair_iff replies (fun _ _ => true) (g.head a point.1) (h.head b point.2)).mpr
      (by simpa using tags)
    change g.productLocal h a b replies point = true at check
    rw [bad] at check
    cases check)
  exact ⟨prim, by simpa only [Endpoint.unit_observeAt] using fails⟩

include left right in
theorem native_path_refutes (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    {point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies) (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail point)
    (bad : g.productLocal h a b replies point = false) :
    ∃ prim : Primitives Φ (trail.length + 1),
      ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) 0 ≤
        Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) 0 := by
  obtain ⟨prim, separates⟩ := path_refutes (left := left) (right := right) walk bad
  exact ⟨prim, by rwa [g.observe_entry raw hg, h.observe_entry raw' hh]⟩

theorem refutation_has_mismatch {σ : Type v} (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s) :
    ∃ point trail, g.searchProduct h a b replies left right = .mismatch point trail := by
  have correct := g.searchProduct_correct h a b replies left right
  cases found : g.searchProduct h a b replies left right with
  | mismatch point trail => exact ⟨point, trail, rfl⟩
  | accepted pairs =>
    rw [found] at correct
    exact (failed (g.checkProduct_sound h raw raw' hg hh a b replies pairs correct.1 prim s)).elim

theorem mismatch_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    (∃ point trail, g.searchProduct h a b replies left right = .mismatch point trail) ↔
      ∃ (n : Nat) (prim : Primitives Φ n) (s : Fin n),
        ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s ≤
          Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s := by
  constructor
  · rintro ⟨point, trail, found⟩
    have sound := g.searchProduct_correct h a b replies left right
    rw [found] at sound
    obtain ⟨prim, bad⟩ := native_path_refutes (left := left) (right := right) hg hh sound.1 sound.2
    exact ⟨trail.length + 1, prim, 0, bad⟩
  · rintro ⟨_, prim, s, bad⟩
    exact refutation_has_mismatch hg hh prim s bad

theorem simple_length {point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies) (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail point)
    (simple : (ProductPath.vertices (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail).Nodup) :
    trail.length + 1 ≤ (g.productVisits h a b replies left right).length :=
  ProductSearch.simple_path_bound left right walk simple

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable
