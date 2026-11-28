module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Observer
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Probe.Thms
import Mathlib.Data.Fin.Embedding

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Table
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (CallerEnumeration ConfigurationEnumeration ReplyEnumeration ProductConfig ProductEdge ProductPath
    Head productContains productContains_iff)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ProductSearch
  (visits_exact visits_path simple_path_bound)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag)
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives Primitives model)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty}
  {g : Table S R} {h : Table S T} {a : Payload (R.get g.entry)} {b : Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

omit [DecidableEq Φ] in
private theorem unit_matches (p : Head S R) (q : Head S T) (rel : Packet R → Packet T → Prop) :
    p.MatchesWith (fun i j => (i, Value.unit (α := Unit)) = (j, Value.unit)) rel q ↔ p.Matches rel q := by
  cases p <;> cases q <;> simp [Head.Matches, Head.MatchesWith]

private theorem table_visits_exact :
    let entry : ProductConfig R T := (⟨g.entry, a⟩, ⟨h.entry, b⟩)
    let seen := g.productVisits h a b replies left right
    (seen.map Prod.fst).Nodup ∧
      ∀ p, p ∈ seen.map Prod.fst ↔ ∃ trail, ProductPath (g.productEdges h a b replies left right) entry trail p :=
  visits_exact _ _ left right

theorem mismatch_path {point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (found : g.productMismatch? h a b replies left right = some (point, trail)) :
    ProductPath (g.productEdges h a b replies left right) (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail point ∧
      (g.head left a point.1).checkPair replies (fun _ _ => true) (h.head right b point.2) = false := by
  have listed := List.mem_of_find?_eq_some found
  have path := visits_path (edges := g.productEdges h a b replies left right)
    (entry := (⟨g.entry, a⟩, ⟨h.entry, b⟩)) (left := left) (right := right) listed
  exact ⟨path, by simpa using List.find?_some found⟩

private theorem point_sound {σ : Type v} (good : g.productMismatch? h a b replies left right = none)
    (prim : StatePrimitives Φ σ) (s : σ) :
    g.observeAt left a prim ⟨g.entry, a⟩ s ≤ h.observeAt right b prim ⟨h.entry, b⟩ s := by
  let seen := (g.productVisits h a b replies left right).map Prod.fst
  have exactVisits := (table_visits_exact (g := g) (h := h) (a := a) (b := b) (replies := replies)
    (left := left) (right := right)).2
  let related := productContains seen
  have start : related ⟨g.entry, a⟩ ⟨h.entry, b⟩ = true :=
    (productContains_iff _ _ _).mpr ((exactVisits _).mpr ⟨[], .start⟩)
  apply (observer g left a).closed_relation_sound (observer h right b) prim
    (fun p q => related p q = true) _ start s
  intro p q mem
  change (g.head left a p).MatchesWith (fun i j => (i, Value.unit (α := Unit)) = (j, Value.unit))
    (fun p q => related p q = true) (h.head right b q)
  apply (unit_matches _ _ _).mpr
  apply (Head.checkPair_iff replies related _ _).mp
  rw [Head.checkPair_edges]
  have seenPair : (p, q) ∈ seen := (productContains_iff _ _ _).mp mem
  obtain ⟨visit, listed, atPair⟩ := List.mem_map.mp seenPair
  have localGood := List.find?_eq_none.mp good visit listed
  have localCheck : (g.head left a p).checkPair replies (fun _ _ => true) (h.head right b q) = true := by
    simpa [atPair] using localGood
  refine Bool.and_eq_true_iff.mpr ⟨localCheck, List.all_eq_true.mpr ?_⟩
  intro edge member
  obtain ⟨trail, path⟩ := (exactVisits _).mp seenPair
  exact (productContains_iff _ _ _).mpr ((exactVisits _).mpr ⟨trail ++ [edge], .step path member⟩)

private theorem path_refutes {start point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies left right) start trail point)
    (bad : (g.head left a point.1).checkPair replies (fun _ _ => true) (h.head right b point.2) = false) :
    ∃ prim : Primitives Φ (trail.length + 1),
      ¬ g.observeAt left a prim start.1 0 ≤ h.observeAt right b prim start.2 0 := by
  induction trail generalizing start with
  | nil =>
    have same := walk.nil_end
    subst point
    apply (observer g left a).local_mismatch_refutes (observer h right b) start.1 start.2 0
    intro good
    have tags : (g.head left a start.1).Matches (fun _ _ => True) (h.head right b start.2) :=
      (unit_matches _ _ _).mp good
    have yes : (g.head left a start.1).checkPair replies (fun _ _ => true) (h.head right b start.2) = true :=
      (Head.checkPair_iff replies (fun _ _ => true) _ _).mpr (by simpa using tags)
    rw [bad] at yes
    cases yes
  | cons edge trail ih =>
    obtain ⟨listed, rest⟩ := walk.uncons
    obtain ⟨f, arg, next, next', reply, earlier, later, edgeEq⟩ :=
      Head.product_edge_forms replies listed
    obtain ⟨suffix, separates⟩ := ih rest
    rw [edgeEq] at separates
    exact (observer g left a).prepend_refutation (observer h right b) start.1 start.2 earlier later reply suffix 0 separates

variable {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A} {decodeLeft : Payload A → Payload (R.get g.entry)}
  {decodeRight : Payload A → Payload (T.get h.entry)}

theorem none_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false := by
  unfold Table.checkEntries?
  cases g.checkNative raw <;> cases h.checkNative raw' <;> simp

theorem sound {σ : Type v}
    (accepted : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true)
    (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (model prim (h.visible.bindings (decodeRight input))) s := by
  unfold Table.checkEntries? at accepted
  split at accepted
  · rename_i gate
    obtain ⟨checked, checked'⟩ := Bool.and_eq_true_iff.mp gate
    rw [g.observe_entry raw checked left, h.observe_entry raw' checked' right]
    have good := List.all_eq_true.mp (Option.some.inj accepted) input (callers.complete input)
    exact point_sound (Option.isNone_iff_eq_none.mp good) prim s
  · cases accepted

theorem witness
    (rejected : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    ∃ (input : Payload A) (prim : Primitives Φ n) (s : Fin n),
      ¬ Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings (decodeLeft input))) s ≤
        Shape.denote (withExitUB raw' h.selected) (model prim (h.visible.bindings (decodeRight input))) s := by
  unfold Table.checkEntries? at rejected
  split at rejected
  · rename_i gate
    obtain ⟨checked, checked'⟩ := Bool.and_eq_true_iff.mp gate
    obtain ⟨input, listed, bad⟩ := List.all_eq_false.mp (Option.some.inj rejected)
    cases found : g.productMismatch? h (decodeLeft input) (decodeRight input) replies left right with
    | none => simp [found] at bad
    | some visit =>
      obtain ⟨point, trail⟩ := visit
      obtain ⟨walk, mismatch⟩ := mismatch_path found
      obtain ⟨shortest, path, simple, _⟩ := walk.shortest
      have count : (g.productVisits h (decodeLeft input) (decodeRight input) replies left right).length ≤
          g.cutoff h callers decodeLeft decodeRight replies left right := by
        have mem := List.mem_map_of_mem (f := fun a =>
          (g.productVisits h (decodeLeft a) (decodeRight a) replies left right).length) listed
        rw [Table.cutoff, List.max?_eq_some_max (List.ne_nil_of_mem mem)]
        exact List.le_max_of_mem mem
      have bound := (simple_path_bound left right path simple).trans count
      obtain ⟨small, separates⟩ := path_refutes path mismatch
      let e := Fin.castLEEmb bound
      let n := g.cutoff h callers decodeLeft decodeRight replies left right
      let prim : Primitives Φ n := fun f arg t =>
        if inside : t.val < shortest.length + 1 then
          (small f arg ⟨t.val, inside⟩).mapState e
        else .diverge
      have agree (f : Φ) (arg : Payload (instrSrc f)) (s : Fin (shortest.length + 1)) :
          prim f arg (e s) = (small f arg s).mapState e := dite_eq_left s.isLt
      refine ⟨input, prim, e 0, ?_⟩
      rw [g.observe_entry raw checked left, h.observe_entry raw' checked' right,
        observeAt_mapState g left _ e small prim agree, observeAt_mapState h right _ e small prim agree,
        Behaviour.mapState_le_iff]
      exact separates
  · cases rejected

theorem cutoff_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    let n := g.cutoff h callers decodeLeft decodeRight replies left right
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      ∀ (input : Payload A) (prim : Primitives Φ n) (s : Fin n),
        Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings (decodeLeft input))) s ≤
          Shape.denote (withExitUB raw' h.selected) (model prim (h.visible.bindings (decodeRight input))) s := by
  constructor
  · exact sound
  · intro valid
    cases verdict : g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right with
    | none => simpa [checked, checked'] using none_iff.mp verdict
    | some b =>
      cases b with
      | true => rfl
      | false =>
        obtain ⟨input, prim, s, bad⟩ := witness verdict
        exact (bad (valid input prim s)).elim

theorem accepts_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  refine ⟨fun yes _ => sound yes, fun valid => (cutoff_iff checked checked').mpr ?_⟩
  intro input prim s
  let n := g.cutoff h callers decodeLeft decodeRight replies left right
  let e : Fin n ↪ ULift.{v} (Fin n) := ⟨ULift.up, ULift.up_injective⟩
  let lifted : StatePrimitives Φ (ULift.{v} (Fin n)) := fun f arg t => (prim f arg t.down).mapState e
  have agree (f : Φ) (arg : Payload (instrSrc f)) (t : Fin n) :
      lifted f arg (e t) = (prim f arg t).mapState e := rfl
  have observes := valid _ input lifted (e s)
  rw [g.observe_entry raw checked left, h.observe_entry raw' checked' right,
    observeAt_mapState g left _ e prim lifted agree, observeAt_mapState h right _ e prim lifted agree,
    Behaviour.mapState_le_iff] at observes
  rwa [g.observe_entry raw checked left, h.observe_entry raw' checked' right]

theorem rejects_iff (checked : g.checkNative raw = true) (checked' : h.checkNative raw' = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false ↔
      ¬ g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  have accepted := accepts_iff.{u,v} (replies := replies) (left := left) (right := right)
    (callers := callers) (decodeLeft := decodeLeft) (decodeRight := decodeRight) checked checked'
  rw [← accepted]
  unfold Table.checkEntries?
  simp [checked, checked', Bool.eq_false_iff]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
