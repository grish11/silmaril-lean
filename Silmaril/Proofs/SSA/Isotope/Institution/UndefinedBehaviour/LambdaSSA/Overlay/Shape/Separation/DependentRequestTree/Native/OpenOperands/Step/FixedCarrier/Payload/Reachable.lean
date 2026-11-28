module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Reachable.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Thms
import Mathlib.Data.Fin.Embedding

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.Reachable

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (Typed withExitUB)
open Syntax (Payload Primitives StatePrimitives)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty} {g : Endpoint S R A} {h : Endpoint S T A}
  {a : Payload (R.get g.control.entry)} {b : Payload (T.get h.control.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

private theorem matches_reachable
    (localMatch : ∀ point ∈ (g.control.productVisits h.control a b replies left right).map Prod.fst,
      (g.control.head a point.1).MatchesWith
        (fun i j => (g.returnPacket a point.1 i).raw = (h.returnPacket b point.2 j).raw)
        (fun _ _ => True) (h.control.head b point.2))
    {σ : Type v} (prim : StatePrimitives Φ σ) (s : σ) :
    g.observeAt a prim ⟨g.control.entry, a⟩ s ≤ h.observeAt b prim ⟨h.control.entry, b⟩ s := by
  let visits := (g.control.productVisits h.control a b replies left right).map Prod.fst
  have visited := (g.control.productVisits_exact h.control a b replies left right).2
  have entry : (⟨g.control.entry, a⟩, ⟨h.control.entry, b⟩) ∈ visits :=
    (visited _).mpr ⟨[], .start⟩
  apply g.closed_relation_sound h a b prim (fun p q => (p, q) ∈ visits) _ entry s
  intro p q mem
  have agrees : (g.control.head a p).MatchesWith
      (fun i j => (g.returnPacket a p i).raw = (h.returnPacket b q j).raw)
      (fun _ _ => True) (h.control.head b q) := localMatch (p, q) mem
  cases lower : g.control.head a p with
  | exit i marked =>
    cases upper : h.control.head b q with
    | exit j chosen =>
      cases marked <;> cases chosen
      · simpa only [lower, upper, Head.MatchesWith] using agrees
      · trivial
      · simp only [lower, upper, Head.MatchesWith] at agrees
      · trivial
    | request | diverge => simp only [lower, upper, Head.MatchesWith] at agrees
  | diverge =>
    cases upper : h.control.head b q with
    | diverge => trivial
    | exit _ chosen =>
      cases chosen
      · simp only [lower, upper, Head.MatchesWith] at agrees
      · trivial
    | request => simp only [lower, upper, Head.MatchesWith] at agrees
  | request f arg next =>
    cases upper : h.control.head b q with
    | exit j chosen =>
      cases chosen
      · simp only [lower, upper, Head.MatchesWith] at agrees
      · trivial
    | diverge => simp only [lower, upper, Head.MatchesWith] at agrees
    | request k operand route =>
      rw [lower, upper] at agrees
      obtain ⟨keys, values, _⟩ := agrees
      subst k
      have same : arg = operand := Subtype.ext values
      subst operand
      refine ⟨rfl, rfl, fun reply => ?_⟩
      obtain ⟨trail, path⟩ := (visited _).mp mem
      let e : ProductEdge S R T := (⟨f, reply⟩, next reply.1 reply.2, route reply.1 reply.2)
      have edge : e ∈ g.control.productEdges h.control a b replies (p, q) := by
        unfold Table.productEdges
        simp only [lower, upper, Head.productEdges]
        exact List.mem_map.mpr ⟨reply, replies.complete f reply, rfl⟩
      exact (visited _).mpr ⟨trail ++ [e], .step path edge⟩

theorem witness {σ : Type v} (prim : StatePrimitives Φ σ) (s : σ)
    (bad : ¬ g.observeAt a prim ⟨g.control.entry, a⟩ s ≤ h.observeAt b prim ⟨h.control.entry, b⟩ s) :
    ∃ (test : Primitives Φ (g.reachableCutoff h a b replies left right))
      (t : Fin (g.reachableCutoff h a b replies left right)),
      ¬ g.observeAt a test ⟨g.control.entry, a⟩ t ≤ h.observeAt b test ⟨h.control.entry, b⟩ t := by
  classical
  have missing : ¬ ∀ point ∈ (g.control.productVisits h.control a b replies left right).map Prod.fst,
      (g.control.head a point.1).MatchesWith
        (fun i j => (g.returnPacket a point.1 i).raw = (h.returnPacket b point.2 j).raw)
        (fun _ _ => True) (h.control.head b point.2) :=
    fun agreement => bad (matches_reachable agreement prim s)
  push Not at missing
  obtain ⟨point, mem, mismatch⟩ := missing
  obtain ⟨trail, walk⟩ := ((g.control.productVisits_exact h.control a b replies left right).2 point).mp mem
  obtain ⟨shortest, path, simple, _⟩ := walk.shortest
  have bound : shortest.length + 1 ≤ g.reachableCutoff h a b replies left right :=
    g.control.simple_product_path_bound (left := left) (right := right) path simple
  obtain ⟨suffix, separates⟩ := g.product_path_refutes h a b path mismatch
  let e := Fin.castLEEmb bound
  let test : Primitives Φ (g.reachableCutoff h a b replies left right) := fun f arg t =>
    if small : t.val < shortest.length + 1 then (suffix f arg ⟨t.val, small⟩).mapState e else .diverge
  have agreesOnImage (f : Φ) (arg : Payload (instrSrc f)) (t : Fin (shortest.length + 1)) :
      test f arg (e t) = (suffix f arg t).mapState e := by
    exact dite_eq_left t.isLt
  refine ⟨test, e 0, ?_⟩
  rw [g.observeAt_mapState e a suffix test agreesOnImage, h.observeAt_mapState e b suffix test agreesOnImage,
    Behaviour.mapState_le_iff]
  exact separates

variable {raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A)}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.control.entry] (Exits A)} {results : Nat}
  {codec : Fin results ≃ Packet (Exits A)}

theorem accepts_sound {σ : Type v} (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (yes : g.checkReachable? h raw raw' codec a b replies left right = some true)
    (prim : StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.control.selected) (Syntax.model prim (g.control.bindings a)) s ≤
      Shape.denote (withExitUB raw' h.control.selected) (Syntax.model prim (h.control.bindings b)) s := by
  let n := g.reachableCutoff h a b replies left right
  rw [Endpoint.checkReachable?, g.acceptance_iff h raw raw' codec a b replies left right
    ⟨List.finRange n, List.mem_finRange⟩ hg hh] at yes
  rw [g.observe_entry_state raw hg, h.observe_entry_state raw' hh]
  by_contra bad
  obtain ⟨test, t, fails⟩ := witness (replies := replies) (left := left) (right := right) prim s bad
  exact fails (by simpa only [g.observe_entry_state raw hg, h.observe_entry_state raw' hh] using yes test t)

theorem accepts_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkReachable? h raw raw' codec a b replies left right = some true ↔
      ∀ (σ : Type) (prim : StatePrimitives Φ σ) (s : σ),
        Shape.denote (withExitUB raw g.control.selected) (Syntax.model prim (g.control.bindings a)) s ≤
          Shape.denote (withExitUB raw' h.control.selected) (Syntax.model prim (h.control.bindings b)) s := by
  refine ⟨fun yes _ prim s => accepts_sound hg hh yes prim s, ?_⟩
  intro all
  let n := g.reachableCutoff h a b replies left right
  rw [Endpoint.checkReachable?, g.acceptance_iff h raw raw' codec a b replies left right
    ⟨List.finRange n, List.mem_finRange⟩ hg hh]
  exact all _

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.Reachable
