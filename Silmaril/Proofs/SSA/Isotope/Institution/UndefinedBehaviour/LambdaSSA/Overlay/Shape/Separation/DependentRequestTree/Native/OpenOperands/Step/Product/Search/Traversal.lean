module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet)
open Syntax (Payload)
open ProductSearch (Visit discover scan)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {edges : ProductConfig R T → List (ProductEdge S R T)}

private theorem keep_iff (removed pair : ProductConfig R T) :
    (!productContains [removed] pair.1 pair.2) = true ↔ pair ≠ removed := by
  simp [← Bool.not_eq_true, productContains_iff]

private theorem discover_some {remaining : List (ProductConfig R T)} {seen : List (Visit S R T)}
    {visit : Visit S R T} (found : discover edges remaining seen = some visit) :
    ∃ origin ∈ seen, ∃ edge ∈ edges origin.1, edge.2 ∈ remaining ∧
      visit = (edge.2, origin.2 ++ [edge]) := by
  unfold discover at found
  obtain ⟨⟨p, path⟩, member, hit⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨edge, listed, picked⟩ := List.exists_of_findSome?_eq_some hit
  split at picked
  · exact ⟨(p, path), member, edge, listed, (productContains_iff _ _ _).mp ‹_ = true›,
      (Option.some.inj picked).symm⟩
  · cases picked

private theorem discover_none {remaining : List (ProductConfig R T)} {seen : List (Visit S R T)}
    (found : discover edges remaining seen = none)
    (origin : Visit S R T) (member : origin ∈ seen) (edge : ProductEdge S R T) (listed : edge ∈ edges origin.1) :
    edge.2 ∉ remaining := by
  unfold discover at found
  have none := List.findSome?_eq_none_iff.mp (List.findSome?_eq_none_iff.mp found origin member) edge listed
  intro mem
  simp [show productContains remaining edge.2.1 edge.2.2 = true from (productContains_iff _ _ _).mpr mem] at none

/-- The inventory bounds the number of discoveries. Every recorded path
is valid and the final inventory of visited configurations is closed. -/
theorem scan_spec (start : ProductConfig R T) (fuel : Nat)
    (remaining : List (ProductConfig R T)) (seen : List (Visit S R T))
    (bound : remaining.length ≤ fuel)
    (cover : ∀ p, p ∈ remaining ∨ p ∈ seen.map Prod.fst)
    (paths : ∀ v ∈ seen, ProductPath edges start v.2 v.1)
    (distinct : (seen.map Prod.fst).Nodup)
    (disjoint : ∀ p ∈ remaining, p ∉ seen.map Prod.fst) :
    let out := scan edges fuel remaining seen
    (∀ v ∈ seen, v ∈ out) ∧
      (∀ v ∈ out, ProductPath edges start v.2 v.1) ∧
      (∀ v ∈ out, ∀ edge ∈ edges v.1, edge.2 ∈ out.map Prod.fst) ∧
      (out.map Prod.fst).Nodup := by
  induction fuel generalizing remaining seen with
  | zero =>
    have empty : remaining = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero bound)
    exact ⟨fun _ h => h, paths, fun v hv edge he => (cover edge.2).resolve_left (by simp [empty]), distinct⟩
  | succ fuel ih =>
    rw [scan]
    cases found : discover edges remaining seen with
    | none =>
      exact ⟨fun _ h => h, paths, fun v hv edge he =>
        (cover edge.2).resolve_left (discover_none found v hv edge he), distinct⟩
    | some visit =>
      obtain ⟨parent, listed, edge, member, active, rfl⟩ := discover_some found
      let visit : Visit S R T := (edge.2, parent.2 ++ [edge])
      let rest := remaining.filter fun p => !productContains [visit.1] p.1 p.2
      have shrinks : rest.length < remaining.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨edge.2, active, fun kept => (keep_iff visit.1 edge.2).mp kept rfl⟩
      have cover' (p) : p ∈ rest ∨ p ∈ (visit :: seen).map Prod.fst := by
        obtain left | right := cover p
        · by_cases same : p = visit.1
          · exact .inr (by simp [same])
          · exact .inl (List.mem_filter.mpr ⟨left, (keep_iff _ _).mpr same⟩)
        · exact .inr (List.mem_cons_of_mem _ right)
      have paths' (v) (hv : v ∈ visit :: seen) : ProductPath edges start v.2 v.1 := by
        rcases List.mem_cons.mp hv with rfl | prior
        · exact .step (paths parent listed) member
        · exact paths v prior
      have distinct' : ((visit :: seen).map Prod.fst).Nodup :=
        List.nodup_cons.mpr ⟨disjoint _ active, distinct⟩
      have disjoint' (p) (hp : p ∈ rest) : p ∉ (visit :: seen).map Prod.fst := by
        obtain ⟨prior, kept⟩ := List.mem_filter.mp hp
        exact fun mem => (List.mem_cons.mp mem).elim ((keep_iff _ _).mp kept) (disjoint _ prior)
      obtain ⟨retained, valid, closed, unique⟩ :=
        ih rest (visit :: seen) (Nat.lt_succ_iff.mp (shrinks.trans_le bound)) cover' paths' distinct' disjoint'
      exact ⟨fun v hv => retained v (List.mem_cons_of_mem _ hv), valid, closed, unique⟩

theorem check_pair_edges [DecidableEq Φ] (replies : ReplyEnumeration S)
    (rel : Packet R → Packet T → Bool) (p : Head S R) (q : Head S T) :
    p.checkPair replies rel q =
      (p.checkPair replies (fun _ _ => true) q &&
        (p.productEdges replies q).all fun edge => rel edge.2.1 edge.2.2) := by
  cases p with
  | exit i marked =>
    cases q with
    | exit j marked' => cases marked <;> cases marked' <;> simp [Head.checkPair, Head.productEdges]
    | request | diverge => cases marked <;> rfl
  | diverge =>
    cases q with
    | exit i marked => cases marked <;> rfl
    | request | diverge => rfl
  | request f arg next =>
    cases q with
    | exit i marked => cases marked <;> rfl
    | diverge => rfl
    | request g arg' next' =>
      simp only [Head.checkPair, Head.productEdges]
      split
      · simp [*, List.all_map, Function.comp_def]
      · simp [*]

theorem head_edge_forms [DecidableEq Φ] (replies : ReplyEnumeration S)
    {lower : Head S R} {upper : Head S T} {edge : ProductEdge S R T}
    (listed : edge ∈ lower.productEdges replies upper) :
    ∃ (f : Φ) (arg : Payload (instrSrc f))
      (next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R)
      (next' : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T)
      (reply : Packet (S.replies f)),
      lower = .request f arg next ∧ upper = .request f arg next' ∧
      edge = (⟨f, reply⟩, next reply.1 reply.2, next' reply.1 reply.2) := by
  cases lower with
  | exit | diverge => simp [Head.productEdges] at listed
  | request f arg next =>
    cases upper with
    | exit | diverge => simp [Head.productEdges] at listed
    | request op' operand' next' =>
      rw [Head.productEdges] at listed
      split at listed
      · rename_i matchQuery
        obtain ⟨keys, values⟩ := Prod.mk.inj matchQuery
        subst op'
        have operands : arg = operand' := Subtype.ext values
        subst operand'
        obtain ⟨reply, _, rfl⟩ := List.mem_map.mp listed
        exact ⟨f, arg, next, next', reply, rfl, rfl, rfl⟩
      · simp at listed

section Edges

variable {g : Table S R} {h : Table S T}
  {caller : Payload (R.get g.entry)} {caller' : Payload (T.get h.entry)}

theorem edge_forms [DecidableEq Φ] (replies : ReplyEnumeration S)
    {p : ProductConfig R T} {edge : ProductEdge S R T}
    (listed : edge ∈ g.productEdges h caller caller' replies p) :
    ∃ (f : Φ) (arg : Payload (instrSrc f))
      (next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R)
      (next' : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T)
      (reply : Packet (S.replies f)),
      g.head caller p.1 = .request f arg next ∧ h.head caller' p.2 = .request f arg next' ∧
      edge = (⟨f, reply⟩, next reply.1 reply.2, next' reply.1 reply.2) :=
  head_edge_forms replies listed

end Edges

section Paths

variable {start point : ProductConfig R T} {trail : List (ProductEdge S R T)}

private theorem path_front (walk : ProductPath edges start trail point) :
    match trail with
    | [] => start = point
    | edge :: tail => edge ∈ edges start ∧ ProductPath edges edge.2 tail point := by
  induction walk with
  | start => rfl
  | @step past p edge _ listed ih =>
    cases past with
    | nil =>
      change start = p at ih
      subst p
      exact ⟨listed, .start⟩
    | cons head tail => exact ⟨ih.1, .step ih.2 listed⟩

theorem path_nil (walk : ProductPath edges start [] point) : start = point :=
  path_front walk

theorem path_uncons {edge : ProductEdge S R T}
    (walk : ProductPath edges start (edge :: trail) point) :
    edge ∈ edges start ∧ ProductPath edges edge.2 trail point :=
  path_front walk

private theorem vertices_snoc (start : ProductConfig R T) (trail : List (ProductEdge S R T))
    (edge : ProductEdge S R T) :
    ProductPath.vertices start (trail ++ [edge]) = ProductPath.vertices start trail ++ [edge.2] := by
  simp [ProductPath.vertices, List.map_append]

private theorem vertex_prefix (walk : ProductPath edges start trail point) {p : ProductConfig R T}
    (visited : p ∈ ProductPath.vertices start trail) :
    ∃ prior, ProductPath edges start prior p ∧ prior.length ≤ trail.length := by
  induction walk with
  | start =>
    have same : p = start := List.mem_singleton.mp visited
    subst p
    exact ⟨[], .start, le_rfl⟩
  | @step past q edge walk listed ih =>
    have split : p ∈ ProductPath.vertices start past ∨ p = edge.2 := by
      simpa only [vertices_snoc, List.mem_append, List.mem_singleton] using visited
    rcases split with prior | rfl
    · obtain ⟨priorPath, path, shorter⟩ := ih prior
      exact ⟨priorPath, path, shorter.trans (by simp)⟩
    · exact ⟨_, .step walk listed, le_rfl⟩

private theorem shorten (walk : ProductPath edges start trail point)
    (repeated : ¬ (ProductPath.vertices start trail).Nodup) :
    ∃ prior, ProductPath edges start prior point ∧ prior.length < trail.length := by
  classical
  induction walk with
  | start => exact (repeated (by simp [ProductPath.vertices])).elim
  | @step past q edge walk listed ih =>
    by_cases seen : edge.2 ∈ ProductPath.vertices start past
    · obtain ⟨prior, path, length⟩ := vertex_prefix walk seen
      exact ⟨prior, path, by simpa using Nat.lt_succ_of_le length⟩
    · have repeated' : ¬ (ProductPath.vertices start past).Nodup := by
        intro simple
        apply repeated
        rw [vertices_snoc, List.nodup_append]
        refine ⟨simple, by simp, ?_⟩
        intro x hx y hy
        obtain rfl := List.mem_singleton.mp hy
        exact fun eq => seen (eq ▸ hx)
      obtain ⟨prior, path, length⟩ := ih repeated'
      exact ⟨prior ++ [edge], .step path listed, by simpa using length⟩

theorem path_shortest (walk : ProductPath edges start trail point) :
    ∃ shortest, ProductPath edges start shortest point ∧
      (ProductPath.vertices start shortest).Nodup ∧
      ∀ other, ProductPath edges start other point → shortest.length ≤ other.length := by
  classical
  let attainable (n : Nat) := ∃ way, ProductPath edges start way point ∧ way.length = n
  have existsLen : ∃ n, attainable n := ⟨trail.length, trail, walk, rfl⟩
  obtain ⟨path, valid, len⟩ := Nat.find_spec existsLen
  have minimal (other) (walk' : ProductPath edges start other point) : path.length ≤ other.length := by
    rw [len]
    exact Nat.find_min' existsLen ⟨other, walk', rfl⟩
  refine ⟨path, valid, ?_, minimal⟩
  by_contra repeated
  obtain ⟨shorter, walk', less⟩ := shorten valid repeated
  exact (Nat.not_lt_of_ge (minimal shorter walk')) less

theorem path_covered (walk : ProductPath edges start trail point) (domain : List (ProductConfig R T))
    (initial : start ∈ domain)
    (closed : ∀ p ∈ domain, ∀ edge ∈ edges p, edge.2 ∈ domain) :
    point ∈ domain ∧ ProductPath.vertices start trail ⊆ domain := by
  induction walk with
  | start => exact ⟨initial, by simpa [ProductPath.vertices]⟩
  | @step past p edge _ member ih =>
    have destination := closed p ih.1 edge member
    refine ⟨destination, ?_⟩
    intro x visited
    have split : x ∈ ProductPath.vertices start past ∨ x = edge.2 := by
      simpa only [vertices_snoc, List.mem_append, List.mem_singleton] using visited
    exact split.elim (@ih.2 x) (fun eq => eq ▸ destination)

end Paths

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
